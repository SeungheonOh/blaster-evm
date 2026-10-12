import EvmBlaster
import Blaster

/-!
# `Token`: balances in a mapping

`contracts/Token.sol`: `balanceOf` (mapping at slot 0), `totalSupply` (slot 1),
`minter` (slot 2). Solidity stores `balanceOf[a]` at slot `keccak256(a ‖ 0)`, which the
machine obtains from the world as `world (.keccak 64 [a, 0])`.

keccak256 is uninterpreted, so properties relating different balances need assumptions
about it: injectivity (distinct holders have distinct slots) and that hashes do not hit
the slots of `totalSupply` and `minter`. These are the standard idealisations of
collision resistance, stated as hypotheses on the world.
-/

namespace Examples.Token
open Evm

#evm_contract_file Token "contracts/build/Token.bin-runtime"

def supplySlot : Nat := 1
def minterSlot : Nat := 2

/-- The storage slot of `balanceOf[a]`. -/
def balanceSlot (world : Query → Nat) (a : Nat) : Nat := world (.keccak 64 [a, 0])

/-- `balanceOf[a]` at the start of the call. -/
def balance (world : Query → Nat) (a : Nat) : Nat := World.storage world (balanceSlot world a)

/-- `balanceOf[a]` after the call. -/
def balance' (world : Query → Nat) (f : Frame) (a : Nat) : Nat := f.sload world (balanceSlot world a)

/-- Only the minter changes the total supply. -/
theorem supply_changes_only_by_minter (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    World.KeccakAbove world 3 →
    (execute Token env world 3000).onSuccess (fun f =>
      f.sload world supplySlot ≠ World.storage world supplySlot →
        env.msg.caller = World.storage world minterSlot % U160) := by
  blaster

/-- The minter is fixed. -/
theorem minter_immutable (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    World.KeccakAbove world 3 →
    (execute Token env world 3000).onSuccess (fun f =>
      f.sload world minterSlot = World.storage world minterSlot) := by
  blaster

/-- Funds only move with the holder's authorisation: nobody but `a` can decrease
    `balanceOf[a]`. -/
theorem only_holder_decreases_balance (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    World.KeccakInjective world → World.KeccakAbove world 3 →
    (execute Token env world 3000).onSuccess (fun f =>
      ∀ a, a < U160 → balance' world f a < balance world a → env.msg.caller = a) := by
  blaster

/-- `transfer(to, amount)` moves exactly `amount` from the caller to `to` and touches no
    other balance. -/
theorem transfer_conserves (env : Env) (world : Query → Nat) (to amount : Nat) :
    env.WF → World.WF world →
    World.KeccakInjective world → World.KeccakAbove world 3 →
    env.msg.calldata = .ofAbi 0xa9059cbb [to, amount] →
    env.msg.caller ≠ to →
    (execute Token env world 3000).onSuccess (fun f =>
      balance' world f env.msg.caller + balance' world f to =
        balance world env.msg.caller + balance world to ∧
      balance' world f env.msg.caller = balance world env.msg.caller - amount ∧
      ∀ a, a < U160 → a ≠ env.msg.caller → a ≠ to → balance' world f a = balance world a) := by
  blaster

/-- `transfer` succeeds whenever the caller has the funds and the recipient's balance does
    not overflow. -/
theorem transfer_succeeds (env : Env) (world : Query → Nat) (to amount : Nat) :
    env.WF → World.WF world →
    World.KeccakInjective world → World.KeccakAbove world 3 →
    env.msg.calldata = .ofAbi 0xa9059cbb [to, amount] →
    env.msg.callvalue = 0 →
    to < U160 → env.msg.caller ≠ to →
    amount ≤ balance world env.msg.caller →
    balance world to + amount < U256 →
    (execute Token env world 3000).succeedsWith (fun f =>
      balance' world f to = balance world to + amount) := by
  blaster

/-! ### The keccak assumptions are needed

Without them Blaster finds the counterexamples: a hash may collide with the slot of
`totalSupply`, and two holders may share a balance slot. (`solve-result: 1` asserts the
statement is falsified.) -/

#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat),
    env.WF → World.WF world →
    (execute Token env world 3000).onSuccess (fun f =>
      f.sload world supplySlot ≠ World.storage world supplySlot →
        env.msg.caller = World.storage world minterSlot % U160)]

#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat),
    env.WF → World.WF world → World.KeccakAbove world 3 →
    (execute Token env world 3000).onSuccess (fun f =>
      ∀ a, a < U160 → balance' world f a < balance world a → env.msg.caller = a)]

end Examples.Token
