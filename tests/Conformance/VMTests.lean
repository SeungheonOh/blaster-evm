import Conformance.Driver

/-!
# Conformance: the legacy VM tests

The `VMTests` of `ethereum/tests` (Constantinople fork, kept in `ethereum/legacytests`)
execute one piece of code in a given environment, without a transaction around it: the
call value is not transferred and nothing is charged up front. They expect either an
exceptional halt (no `post` field) or a successful execution with the given post-state of
the executing account, return data (`out`) and logs (`logs`, the hash of their RLP list).
Calls are recorded in `callcreates` rather than executed (none of the tests makes one).

What is compared, for an expected success: the storage and balance of the executing
account, the return data, the logs hash, and the absence of calls. The remaining gas
(`gas`) is not: the machine does not model gas.
-/

namespace Conformance
open Lean Evm

def runVMTest (t : Json) : Except String Verdict := do
  let ex ← field t "exec"
  let envJ ← field t "env"
  let pre ← parseAccounts (← field t "pre")
  let address ← num ex "address"
  let value ← num ex "value"
  let number ← num envJ "currentNumber"
  let self := pre.getD address ⟨0, 0, #[], {}⟩
  let env : Env :=
    { block := { coinbase := ← num envJ "currentCoinbase"
                 timestamp := ← num envJ "currentTimestamp"
                 number
                 -- `DIFFICULTY` (0x44) became `PREVRANDAO`
                 prevrandao := ← num envJ "currentDifficulty"
                 gaslimit := ← num envJ "currentGasLimit"
                 chainid := 1, basefee := 0, blobbasefee := 0 }
      tx := { origin := ← num ex "origin", gasprice := ← num ex "gasPrice" }
      msg := { address, caller := ← num ex "caller", callvalue := value
               calldata := Calldata.ofBytes (← bytes ex "data") }
      -- the value is not transferred: the machine credits it, so start below by as much
      balance := self.balance - value }
  let world : Query → Nat
    | .storage k => self.storage.getD k 0
    | .keccak n ws => Tests.Keccak.keccak256 (Tests.Keccak.bytesOfChunks n ws)
    | .balance a => (pre.get? a).map (·.balance) |>.getD 0
    | .extcodesize a => (pre.get? a).map (·.code.size) |>.getD 0
    | .extcodehash a => codeHash pre a
    -- the test environment's convention for the hashes of the 256 previous blocks
    | .blockhash n =>
      if n < number ∧ number ≤ n + 256 then Tests.Keccak.keccak256 (toString n).toUTF8.data
      else 0
    | .callSuccess _ => 1
    | _ => 0
  let c := Contract.ofBytes (← bytes ex "code")
  let g : GasCtx := { original := (self.storage.getD · 0), dead := isDead pre, cancun := false }
  let run := runCall c env world g (← num ex "gas")
  let cx := memCtx c env world
  if !hasField t "post" then
    -- an exceptional halt is expected
    return match run.ending with
      | .halted .exception => .pass
      | .outOfGas _ => .passOutOfGas
      | .halted (.unsupported i) => .outOfScope s!"unsupported {instrName i}"
      | .halted (.success ..) =>
        if run.readsGas then .inconclusive "reads GAS"
        else .fail s!"expected an exceptional halt, got success after {run.steps} steps"
      | .halted (.revert _) => .fail "expected an exceptional halt, got a revert"
      | .halted .outOfFuel => .fail "out of fuel"
  let post ← parseAccounts (← field t "post")
  let expected := post.getD address ⟨0, 0, #[], {}⟩
  match run.ending with
  | .halted (.success f out) =>
    let storage := storageAfter self.storage f
    let outBytes := sliceBytes cx out
    let logs := frameLogs cx address f
    let mut diffs : List String := []
    if storageList storage != storageList expected.storage then
      diffs := diffs ++ [s!"storage {showStorage storage}, expected {showStorage expected.storage}"]
    if f.balance != expected.balance then
      diffs := diffs ++ [s!"balance {f.balance}, expected {expected.balance}"]
    if outBytes != (← bytes t "out") then diffs := diffs ++ ["return data"]
    if logsHash logs != (← num t "logs") then diffs := diffs ++ [s!"logs ({logs.length} logs)"]
    if !f.calls.isEmpty then diffs := diffs ++ ["unexpected calls"]
    if diffs.isEmpty then return .pass
    if run.readsGas then return .inconclusive s!"reads GAS; {diffs}"
    return .fail (", ".intercalate diffs)
  | .halted (.unsupported i) => return .outOfScope s!"unsupported {instrName i}"
  | .outOfGas pc => return .fail s!"expected success, but the gas bound is exceeded at pc {pc}"
  | .halted .exception => return .fail s!"expected success, got an exceptional halt after {run.steps} steps"
  | .halted (.revert _) => return .fail "expected success, got a revert"
  | .halted .outOfFuel => return .fail "out of fuel"

end Conformance
