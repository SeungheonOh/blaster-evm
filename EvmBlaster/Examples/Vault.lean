import EvmBlaster
import Blaster

/-!
# `Vault`: Ether released only to the beneficiary, only after the deadline

`contracts/Vault.sol`: `owner` (slot 0), `beneficiary` (slot 1), `unlockTime` (slot 2).
`withdraw(amount)` sends `amount` wei to the beneficiary with a `CALL`; `extendLock` lets
the owner postpone the deadline.

The outgoing call is answered by the world (`Query.callSuccess 0`, `Query.returnSize 0`,
...): the theorems hold whatever the recipient does, except where an assumption about it
is stated explicitly.
-/

namespace Examples.Vault
open Evm

#evm_contract_file Vault "contracts/build/Vault.bin-runtime"

def ownerSlot : Nat := 0
def beneficiarySlot : Nat := 1
def unlockSlot : Nat := 2

def beneficiary (world : Query → Nat) : Nat := World.storage world beneficiarySlot % U160
def unlockTime (world : Query → Nat) : Nat := World.storage world unlockSlot

/-- Ether only ever leaves the contract towards the beneficiary. -/
theorem transfers_only_to_beneficiary (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f =>
      AllCalls (fun c => c.value ≠ 0 → c.to = beneficiary world) f.calls) := by
  blaster

/-- Ether only leaves when the beneficiary asks, after the deadline. -/
theorem transfers_only_after_unlock (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f =>
      f.valueSent ≠ 0 →
        env.msg.caller = beneficiary world ∧ unlockTime world ≤ env.block.timestamp) := by
  blaster

/-- At most one outgoing call per transaction. -/
theorem at_most_one_call (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f => f.calls.length ≤ 1) := by
  blaster

/-- The deadline can only move forward. -/
theorem unlock_never_decreases (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f =>
      unlockTime world ≤ f.sload world unlockSlot) := by
  blaster

/-- Only the owner moves the deadline. -/
theorem unlock_changes_only_by_owner (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f =>
      f.sload world unlockSlot ≠ unlockTime world →
        env.msg.caller = World.storage world ownerSlot % U160) := by
  blaster

/-- Owner and beneficiary are fixed. -/
theorem roles_immutable (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f =>
      f.sload world ownerSlot = World.storage world ownerSlot ∧
      f.sload world beneficiarySlot = World.storage world beneficiarySlot) := by
  blaster

/-- Balance accounting: what is not sent stays in the contract. (Assuming the vault is
    not its own beneficiary: a call to oneself moves no Ether, as the counterexample
    found without this hypothesis shows.) -/
theorem balance_accounting (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    beneficiary world ≠ env.msg.address →
    (execute Vault env world 3000).onSuccess (fun f =>
      f.balance + f.valueSent = env.balance + env.msg.callvalue) := by
  blaster

/-- Liveness, under an assumption about the chain: if the beneficiary accepts the
    transfer (the world answers the `0`-th call with success), the beneficiary can withdraw
    any amount up to the balance once the deadline has passed. -/
theorem beneficiary_can_withdraw (env : Env) (world : Query → Nat) (amount : Nat) :
    env.WF → World.WF world →
    env.msg.calldata = .ofAbi 0x2e1a7d4d [amount] →
    env.msg.callvalue = 0 →
    env.msg.caller = beneficiary world →
    unlockTime world ≤ env.block.timestamp →
    amount ≤ env.balance →
    beneficiary world ≠ env.msg.address →
    world (.callSuccess 0) ≠ 0 →
    (execute Vault env world 3000).succeedsWith (fun f =>
      f.valueSent = amount ∧ f.balance = env.balance - amount) := by
  blaster

end Examples.Vault
