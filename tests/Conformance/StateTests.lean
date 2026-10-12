import Conformance.Driver

/-!
# Conformance: the general state tests, Cancun

The `GeneralStateTests` of `ethereum/tests`, filled for Cancun in blockchain-test form
(kept in `ethereum/legacytests`): a block with one transaction on top of a pre-state,
with the expected post-state of every account. Only the `Cancun` entries are run, the
fork the machine models.

A test is in scope when the transaction calls an account with code and the execution
stays in the modelled fragment: no unsupported instruction, and no call to a contract or
a precompile. Calls to accounts without code are answered exactly by the world: they
succeed with empty return data.

The world is the chain during the transaction: the pre-state, except that the sender has
paid for the gas and the blob gas up front and sent the value (the machine credits the
value to the callee). `BLOCKHASH` knows the parent block's hash.

What is compared: the storage of the called account, its balance (unless it is the
coinbase or the sender, whose balances also move with the fees), and the logs bloom of the
block. A failed execution leaves the storage and balance unchanged and emits no logs. When
the machine halts exceptionally, or its execution provably runs out of gas, the block must
also show that the transaction consumed all of its gas, as an exceptional halt does.
-/

namespace Conformance
open Lean Evm

/-- EIP-4844's approximation of `factor * e^(numerator / denominator)`. -/
def fakeExponential (factor numerator denominator : Nat) : Nat := Id.run do
  let mut i := 1
  let mut output := 0
  let mut acc := factor * denominator
  -- the terms decrease from `i > numerator / denominator` on; the bound is never reached
  for _ in [0:100000] do
    if acc == 0 then break
    output := output + acc
    acc := acc * numerator / (denominator * i)
    i := i + 1
  return output / denominator

def isPrecompile (a : Nat) : Bool := 1 ≤ a && a ≤ 10

/-- The EIP-4788 beacon roots contract, whose storage the block writes before running
    its transactions. -/
def beaconRoots : Nat := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02

def runStateTest (t : Json) : Except String Verdict := do
  let blocks ← (← field t "blocks").getArr?
  if blocks.size != 1 then return .outOfScope "several blocks"
  let blk := blocks[0]!
  if hasField blk "expectException" || !hasField blk "blockHeader" then
    return .outOfScope "invalid block or transaction"
  let txs ← (← field blk "transactions").getArr?
  if txs.size != 1 then return .outOfScope "not one transaction"
  let tx := txs[0]!
  if !hasField t "postState" then return .outOfScope "post-state given as a hash"
  let toStr ← str tx "to"
  if toStr == "" then return .outOfScope "contract creation"
  let to ← hexNat toStr
  let pre ← parseAccounts (← field t "pre")
  let some target := pre.get? to | return .outOfScope "no code at the destination"
  if target.code.isEmpty then return .outOfScope "no code at the destination"
  if to == beaconRoots then return .outOfScope "the EIP-4788 contract (written by the block)"
  let hdr ← field blk "blockHeader"
  let number ← num hdr "number"
  let baseFee ← numD hdr "baseFeePerGas" 0
  let blobBaseFee := fakeExponential 1 (← numD hdr "excessBlobGas" 0) 3338477
  let coinbase ← num hdr "coinbase"
  let parentHash ← num hdr "parentHash"
  let sender ← num tx "sender"
  let value ← num tx "value"
  let data ← bytes tx "data"
  let gasLimit ← num tx "gasLimit"
  let gasPrice ←
    if hasField tx "gasPrice" then num tx "gasPrice"
    else do pure (min (← num tx "maxFeePerGas") (baseFee + (← num tx "maxPriorityFeePerGas")))
  let blobHashes ←
    if hasField tx "blobVersionedHashes" then
      (← (← field tx "blobVersionedHashes").getArr?).toList.mapM fun j => do hexNat (← j.getStr?)
    else pure []
  -- the access list: (address, storage keys) pairs
  let accessList ←
    if hasField tx "accessList" then
      (← (← field tx "accessList").getArr?).toList.mapM fun e => do
        let keys ← (← (← field e "storageKeys").getArr?).toList.mapM fun k => do hexNat (← k.getStr?)
        return (← num e "address", keys)
    else pure []
  let intrinsic := intrinsicGas data accessList.length (accessList.foldl (· + ·.2.length) 0)
  if gasLimit < intrinsic then return .outOfScope "invalid transaction"
  let senderBalance := (pre.get? sender).map (·.balance) |>.getD 0
  let upfront := gasLimit * gasPrice + 131072 * blobHashes.length * blobBaseFee + value
  let world : Query → Nat
    | .storage k => target.storage.getD k 0
    | .keccak n ws => Tests.Keccak.keccak256 (Tests.Keccak.bytesOfChunks n ws)
    | .balance a =>
      if a == sender then senderBalance - upfront else (pre.get? a).map (·.balance) |>.getD 0
    | .extcodesize a => (pre.get? a).map (·.code.size) |>.getD 0
    -- the sender exists: its nonce has been incremented
    | .extcodehash a =>
      if a == sender && isDead pre a then Tests.Keccak.keccak256 #[] else codeHash pre a
    | .blockhash n => if n + 1 == number then parentHash else 0
    | .blobhash i => blobHashes.getD i 0
    | .callSuccess _ => 1
    | _ => 0
  let env : Env :=
    { block := { coinbase, timestamp := ← num hdr "timestamp", number
                 prevrandao := ← num hdr "mixHash", gaslimit := ← num hdr "gasLimit"
                 chainid := 1, basefee := baseFee, blobbasefee := blobBaseFee }
      tx := { origin := sender, gasprice := gasPrice }
      msg := { address := to, caller := sender, callvalue := value
               calldata := Calldata.ofBytes data }
      balance := if to == sender then senderBalance - upfront else target.balance }
  let c := Contract.ofBytes target.code
  let g : GasCtx := { original := (target.storage.getD · 0), dead := isDead pre, cancun := true }
  -- warm at the start: sender, recipient, coinbase (EIP-3651), precompiles, access list
  let warm : Warm :=
    { addrs := Std.HashSet.ofList ([sender, to, coinbase] ++ (List.range 10).map (· + 1)
                 ++ accessList.map (·.1))
      slots := Std.HashSet.ofList (accessList.filter (·.1 == to) |>.flatMap (·.2)) }
  let run := runCall c env world g (gasLimit - intrinsic) warm
  if let .halted (.unsupported i) := run.ending then
    return .outOfScope s!"unsupported {instrName i}"
  -- scope: calls only to accounts without code
  let calls := match run.ending with
    | .halted (.success f _) => f.calls
    | _ => run.last.calls
  if let some r := calls.find? fun r =>
      isPrecompile r.to || r.to == to || !((pre.get? r.to).map (·.code.isEmpty) |>.getD true) then
    return .outOfScope (if isPrecompile r.to then "calls a precompile" else "calls a contract")
  -- the effects
  let cx := memCtx c env world
  let (storage, balance, logs) ← match run.ending with
    | .halted (.success f _) => pure (storageAfter target.storage f, f.balance, frameLogs cx to f)
    | _ => pure (target.storage, env.balance, [])
  let post ← parseAccounts (← field t "postState")
  let expected := post.getD to ⟨0, 0, #[], {}⟩
  let mut diffs : List String := []
  if storageList storage != storageList expected.storage then
    diffs := diffs ++ [s!"storage {showStorage storage}, expected {showStorage expected.storage}"]
  if to != coinbase && to != sender && balance != expected.balance then
    diffs := diffs ++ [s!"balance {balance}, expected {expected.balance}"]
  if logsBloom logs != (← num hdr "bloom") then diffs := diffs ++ [s!"logs bloom ({logs.length} logs)"]
  -- an exceptional halt (running out of gas included) consumes all the gas
  let exceptional := match run.ending with
    | .halted .exception | .outOfGas _ => true
    | _ => false
  let gasUsed ← num hdr "gasUsed"
  if exceptional && gasUsed != gasLimit then
    diffs := diffs ++ [s!"gas used {gasUsed} of {gasLimit}: no exceptional halt"]
  let ending := match run.ending with
    | .halted (.success ..) => "success"
    | .halted (.revert _) => "revert"
    | .halted .exception => "exceptional halt"
    | .outOfGas pc => s!"gas bound exceeded at pc {pc}"
    | _ => "other"
  if diffs.isEmpty then
    return match run.ending with
      | .outOfGas _ => .passOutOfGas
      | _ => .pass
  if run.readsGas then return .inconclusive s!"reads GAS; {ending}; {diffs}"
  return .fail s!"{ending} after {run.steps} steps: {", ".intercalate diffs}"

end Conformance
