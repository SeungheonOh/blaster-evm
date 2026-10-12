import EvmBlaster
import Blaster

/-!
# `Config`: a parameter store guarded by an owner

`contracts/Config.sol`: `owner` (slot 0), `fee` (slot 1), `maxFee` (slot 2);
`setFee(uint256)` and `transferOwnership(address)` are restricted to the owner.

Every theorem is about the deployed runtime bytecode, executed symbolically, for every
environment and chain state, and (unless stated) for *every* calldata: any selector and
any arguments.
-/

namespace Examples.Config
open Evm

#evm_contract_file Config "contracts/build/Config.bin-runtime"

/-- Storage slot of the owner. -/
def ownerSlot : Nat := 0
def feeSlot : Nat := 1
def maxFeeSlot : Nat := 2

/-- The owner recorded in storage at the start of the call. -/
def owner (world : Query → Nat) : Nat := World.storage world ownerSlot % U160

/-- Only the owner can change the fee. -/
theorem fee_changes_only_by_owner (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Config env world 3000).onSuccess (fun f =>
      f.sload world feeSlot ≠ World.storage world feeSlot → env.msg.caller = owner world) := by
  blaster

/-- Only the owner can change the owner, and never to the zero address. -/
theorem owner_changes_only_by_owner (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Config env world 3000).onSuccess (fun f =>
      f.sload world ownerSlot % U160 ≠ owner world →
        env.msg.caller = owner world ∧ f.sload world ownerSlot % U160 ≠ 0) := by
  blaster

/-- `maxFee` is never written: no function of the contract can raise the cap. -/
theorem maxFee_immutable (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Config env world 3000).onSuccess (fun f =>
      f.sload world maxFeeSlot = World.storage world maxFeeSlot) := by
  blaster

/-- A changed fee respects the cap. -/
theorem fee_within_cap (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Config env world 3000).onSuccess (fun f =>
      f.sload world feeSlot ≠ World.storage world feeSlot →
        f.sload world feeSlot ≤ World.storage world maxFeeSlot) := by
  blaster

/-- The contract is non-payable: a call carrying Ether always fails. -/
theorem rejects_ether (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → env.msg.callvalue ≠ 0 →
    (execute Config env world 3000).isFailure := by
  blaster

/-- The contract never calls out. -/
theorem no_external_calls (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Config env world 3000).onSuccess (fun f => f.calls = []) := by
  blaster

/-- Functional correctness of `setFee`: the owner can set any fee within the cap, and the
    change is logged with the `FeeChanged(old, new)` event. -/
theorem setFee_by_owner (env : Env) (world : Query → Nat) (newFee : Nat) :
    env.WF → World.WF world →
    env.msg.calldata = .ofAbi 0x69fe0e2d [newFee] →
    env.msg.callvalue = 0 →
    env.msg.caller = owner world →
    newFee ≤ World.storage world maxFeeSlot →
    (execute Config env world 3000).succeedsWith (fun f =>
      f.sload world feeSlot = newFee ∧
      f.sload world ownerSlot = World.storage world ownerSlot ∧
      f.logs.length = 1) := by
  blaster

/-- Any other caller is rejected. -/
theorem setFee_by_other_reverts (env : Env) (world : Query → Nat) (newFee : Nat) :
    env.WF → World.WF world →
    env.msg.calldata = .ofAbi 0x69fe0e2d [newFee] →
    env.msg.caller ≠ owner world →
    (execute Config env world 3000).isFailure := by
  blaster

/-! ## Over any sequence of calls

The theorems above are about one call, in any chain state. A property of the contract's
whole life follows by induction over the calls (`runCalls`), with the single-call theorems
as the induction step: Blaster for the step, Lean for the induction. -/

/-- Every value stored is a word, so the next call's world is well formed. -/
theorem stores_words (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Config env world 3000).onSuccess (fun f => ∀ k, f.sload world k < U256) := by
  blaster

theorem withStorage_WF {world : Query → Nat} {σ : Nat → Nat} :
    World.WF world → (∀ k, σ k < U256) → World.WF (World.withStorage world σ) := by
  intro hw hσ q
  cases q <;> first | exact hσ _ | exact hw _

/-- Over any sequence of calls in which the owner sends nothing, neither the owner nor the
    fee ever changes, whatever happens on the rest of the chain in between. -/
theorem owner_and_fee_stable (txs : List (Env × (Query → Nat))) (σ : Nat → Nat) :
    (∀ k, σ k < U256) →
    (∀ tx ∈ txs, tx.1.WF ∧ World.WF tx.2 ∧ tx.1.msg.caller ≠ σ ownerSlot % U160) →
    runCalls Config 3000 σ txs feeSlot = σ feeSlot ∧
    runCalls Config 3000 σ txs ownerSlot % U160 = σ ownerSlot % U160 := by
  induction txs generalizing σ with
  | nil => intro _ _; exact ⟨rfl, rfl⟩
  | cons tx rest ih =>
    obtain ⟨env, world⟩ := tx
    intro hσ hall
    obtain ⟨henv, hworld, hcaller⟩ := hall (env, world) (by simp)
    have hrest : ∀ tx ∈ rest, tx.1.WF ∧ World.WF tx.2 ∧ tx.1.msg.caller ≠ σ ownerSlot % U160 :=
      fun tx htx => hall tx (by simp [htx])
    have hw := withStorage_WF hworld hσ
    have hfee := fee_changes_only_by_owner env _ henv hw
    have hown := owner_changes_only_by_owner env _ henv hw
    have hwords := stores_words env _ henv hw
    simp only [runCalls]
    generalize execute Config env (World.withStorage world σ) 3000 = r at hfee hown hwords ⊢
    cases r with
    | success f out =>
      simp only [Result.onSuccess] at hfee hown hwords
      simp only [Result.storageAfter]
      -- the call's world has storage `σ`, so `f.sload` is `Storage.read σ f.storage`
      have e1 : Storage.read σ f.storage feeSlot = σ feeSlot :=
        Classical.byContradiction fun h => hcaller (hfee h)
      have e0 : Storage.read σ f.storage ownerSlot % U160 = σ ownerSlot % U160 :=
        Classical.byContradiction fun h => hcaller (hown h).1
      have ⟨r1, r0⟩ := ih (Storage.read σ f.storage) hwords fun tx htx => by
        obtain ⟨a, b, c⟩ := hrest tx htx
        exact ⟨a, b, by rw [e0]; exact c⟩
      exact ⟨r1.trans e1, r0.trans e0⟩
    | revert _ | exception => exact ih σ hσ hrest
    | unsupported _ | outOfFuel => exact hfee.elim

end Examples.Config
