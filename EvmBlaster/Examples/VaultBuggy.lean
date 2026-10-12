import EvmBlaster
import Blaster

/-!
# `VaultBuggy`: Blaster finds the attacks

`contracts/VaultBuggy.sol` is `Vault` with two bugs in `extendLock`: it authenticates the
owner with `tx.origin` instead of `msg.sender`, and it no longer refuses to bring the
deadline forward. The properties proved for `Vault` fail here, and Blaster returns
counterexamples (`solve-result: 1` asserts that the statement is falsified).
-/

namespace Examples.VaultBuggy
open Evm

#evm_contract_file VaultBuggy "contracts/build/VaultBuggy.bin-runtime"

def ownerSlot : Nat := 0
def unlockSlot : Nat := 2

/-
Counterexample: `tx.origin = owner` but `msg.sender ≠ owner` (the owner was lured into
calling an attacker contract, which calls `extendLock`). The world is an uninterpreted
function, whose model Blaster does not print; naming the storage values of interest as
variables (`owner`, `unlock`) makes them part of the counterexample.
-/
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (owner unlock : Nat),
    env.WF → World.WF world →
    World.storage world ownerSlot = owner → World.storage world unlockSlot = unlock →
    (execute VaultBuggy env world 3000).onSuccess (fun f =>
      f.sload world unlockSlot ≠ unlock → env.msg.caller = owner % U160)]

-- Counterexample: `extendLock` with a time earlier than the current deadline.
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (unlock : Nat),
    env.WF → World.WF world → World.storage world unlockSlot = unlock →
    (execute VaultBuggy env world 3000).onSuccess (fun f =>
      unlock ≤ f.sload world unlockSlot)]

/-- The transfer properties still hold: the bugs are confined to the deadline. -/
theorem transfers_only_to_beneficiary (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute VaultBuggy env world 3000).onSuccess (fun f =>
      AllCalls (fun c => c.value ≠ 0 → c.to = World.storage world 1 % U160) f.calls) := by
  blaster

end Examples.VaultBuggy
