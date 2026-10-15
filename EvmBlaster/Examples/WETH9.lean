import EvmBlaster
import Blaster

/-!
# WETH9: the deployed mainnet bytecode

`contracts/mainnet/WETH9.bin-runtime` is the runtime bytecode of Wrapped Ether at
`0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2`, fetched with `eth_getCode` (source:
`contracts/mainnet/WETH9.sol.txt`, compiled in 2017 by solc 0.4.x). The theorems below are
about that exact bytecode, for every caller, value, calldata and chain state.

Storage: `name` (slot 0), `symbol` (slot 1), `decimals` (slot 2), `balanceOf` (mapping at
slot 3), `allowance` (nested mapping at slot 4).

Chain-state assumptions:
* `HashesFree`, `World.KeccakAbove`: the hashes the call computes and the statement reads
  do not collide, and hashes avoid the five fixed slots (idealised collision resistance);
* `Mainnet world`: slots 0 and 1 hold the strings "Wrapped Ether" and "WETH", as on
  mainnet. Without it, `name()` and `symbol()` copy a string of symbolic length with a loop
  that symbolic execution cannot bound.
-/

namespace Examples.WETH9
open Evm

#evm_contract_file WETH9 "contracts/mainnet/WETH9.bin-runtime"

def nameWord : Nat := 0x577261707065642045746865720000000000000000000000000000000000001a
def symbolWord : Nat := 0x5745544800000000000000000000000000000000000000000000000000000008

example : Solidity.shortString "Wrapped Ether" = nameWord := by decide
example : Solidity.shortString "WETH" = symbolWord := by decide

/-- The mainnet contents of the string slots. -/
def Mainnet (world : Query → Nat) : Prop :=
  World.storage world 0 = nameWord ∧ World.storage world 1 = symbolWord

/-- Chain-state assumptions shared by all theorems. -/
def Assumptions (world : Query → Nat) : Prop :=
  World.WF world ∧ World.KeccakAbove world 5 ∧ Mainnet world

/-- The hashes of the call and `extra` do not collide. -/
abbrev Hashes (env : Env) (world : Query → Nat) (extra : List HashInput) : Prop :=
  HashesFree WETH9 env world 5000 1 extra

/-- `balanceOf[a]`, before and after the call. -/
def bal (world : Query → Nat) (a : Nat) : Nat := World.storage world (Solidity.mappingSlot world 3 a)
def bal' (world : Query → Nat) (f : Frame) (a : Nat) : Nat :=
  f.sload world (Solidity.mappingSlot world 3 a)

/-- `allowance[o][s]`, before and after the call. -/
def allowSlot (world : Query → Nat) (o s : Nat) : Nat := Solidity.mappingSlot2 world 4 o s
def allow (world : Query → Nat) (o s : Nat) : Nat := World.storage world (allowSlot world o s)
def allow' (world : Query → Nat) (f : Frame) (o s : Nat) : Nat := f.sload world (allowSlot world o s)

/-- Ether only ever leaves WETH towards the caller. -/
theorem ether_only_to_caller (env : Env) (world : Query → Nat) :
    env.WF → Assumptions world → Hashes env world [] →
    (execute WETH9 env world 5000).onSuccess (fun f =>
      AllCalls (fun c => c.value ≠ 0 → c.to = env.msg.caller) f.calls) := by
  blaster

/-- Every wei that leaves is burned from the caller's WETH balance. -/
theorem ether_out_is_burned (env : Env) (world : Query → Nat) :
    env.WF → Assumptions world → Hashes env world [mapKey 3 env.msg.caller] →
    (execute WETH9 env world 5000).onSuccess (fun f =>
      f.valueSent ≠ 0 → bal' world f env.msg.caller + f.valueSent = bal world env.msg.caller) := by
  blaster

/-- Every wei that comes in is credited to the caller. (WETH9 predates checked arithmetic,
    so the credit is modulo `2^256`.) -/
theorem ether_in_is_credited (env : Env) (world : Query → Nat) :
    env.WF → Assumptions world → Hashes env world [mapKey 3 env.msg.caller] →
    (execute WETH9 env world 5000).onSuccess (fun f =>
      env.msg.callvalue ≠ 0 →
        bal' world f env.msg.caller = (bal world env.msg.caller + env.msg.callvalue) % U256) := by
  blaster

/-- Every WETH balance is backed by deposited Ether, so it is far below `2^128` (the
    total Ether supply is about `2^87` wei). -/
def BalancesBounded (world : Query → Nat) : Prop := ∀ a, bal world a < 2 ^ 128

/-- Nobody can take WETH from `a` except `a` itself, or a spender within its allowance,
    which is then consumed (unless it is the infinite allowance `2^256 - 1`).

    `BalancesBounded` is needed: this pre-0.8 bytecode adds to the recipient's balance
    without an overflow check, so from an arbitrary state a transfer could wrap the
    recipient's balance around, a decrease nobody authorised. -/
theorem only_owner_or_spender_debits (env : Env) (world : Query → Nat) (a : Nat) :
    env.WF → Assumptions world → BalancesBounded world → a < U160 →
    Hashes env world (mapKey 3 a :: mapKey2 world 4 a env.msg.caller) →
    (execute WETH9 env world 5000).onSuccess (fun f =>
      bal' world f a < bal world a →
        env.msg.caller = a ∨
        (bal world a - bal' world f a ≤ allow world a env.msg.caller ∧
         (allow world a env.msg.caller = U256 - 1 ∨
          allow' world f a env.msg.caller =
            allow world a env.msg.caller - (bal world a - bal' world f a)))) := by
  blaster

/-- Allowances only change by their owner (`approve`) or by their spender spending them. -/
theorem allowance_changes (env : Env) (world : Query → Nat) (o s : Nat) :
    env.WF → Assumptions world → o < U160 → s < U160 → Hashes env world (mapKey2 world 4 o s) →
    (execute WETH9 env world 5000).onSuccess (fun f =>
      allow' world f o s ≠ allow world o s →
        env.msg.caller = o ∨ (env.msg.caller = s ∧ allow' world f o s < allow world o s)) := by
  blaster

/-- `transfer(dst, wad)` moves `wad` from the caller to `dst` and touches no other balance.
    (`dst < 2^160` is needed: this 2017 bytecode does not reject addresses with dirty upper
    bits, and credits `balanceOf[dst mod 2^160]`.) -/
theorem transfer_conserves (env : Env) (world : Query → Nat) (dst wad a : Nat) :
    env.WF → Assumptions world →
    env.msg.calldata = .ofAbi 0xa9059cbb [dst, wad] → dst < U160 → env.msg.caller ≠ dst →
    Hashes env world [mapKey 3 env.msg.caller, mapKey 3 dst, mapKey 3 a] →
    (execute WETH9 env world 5000).onSuccess (fun f =>
      bal' world f env.msg.caller = bal world env.msg.caller - wad ∧
      bal' world f dst = (bal world dst + wad) % U256 ∧
      f.valueSent = 0 ∧
      (a < U160 → a ≠ env.msg.caller → a ≠ dst → bal' world f a = bal world a)) := by
  blaster

/-- Liveness under a chain-state assumption: a holder can always withdraw up to their
    balance, provided the contract holds the Ether and the transfer to the holder succeeds. -/
theorem withdraw_succeeds (env : Env) (world : Query → Nat) (wad : Nat) :
    env.WF → Assumptions world → Hashes env world [mapKey 3 env.msg.caller] →
    env.msg.calldata = .ofAbi 0x2e1a7d4d [wad] → env.msg.callvalue = 0 →
    env.msg.caller ≠ env.msg.address →
    wad ≤ bal world env.msg.caller → wad ≤ env.balance →
    world (.callSuccess 0) ≠ 0 →
    (execute WETH9 env world 5000).succeedsWith (fun f =>
      f.valueSent = wad ∧ bal' world f env.msg.caller = bal world env.msg.caller - wad) := by
  blaster

/-! ### The assumptions are consistent -/

#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (a : Nat),
    env.WF → Assumptions world → BalancesBounded world → a < U160 →
    Hashes env world (mapKey 3 a :: mapKey2 world 4 a env.msg.caller) → False]

end Examples.WETH9
