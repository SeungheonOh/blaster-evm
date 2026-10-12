import EvmBlaster
import Blaster

/-!
# `Timelock`: parameter changes announced in advance

`contracts/Timelock.sol`: `admin` (slot 0), `fee` (slot 1), `pendingFee` (slot 2), `eta`
(slot 3). The admin queues a new fee with `queueFee`, which becomes executable `DELAY`
(2 days) later; anyone then applies it with `executeFee`. The admin can `cancel` a queued
change.

The point of a timelock is that users see every parameter change coming. The single-call
theorems establish the mechanism; `fee_without_admin` combines them over sequences of
calls: whatever happens, without the admin the fee can only take the value already queued.
-/

namespace Examples.Timelock
open Evm

#evm_contract_file Timelock "contracts/build/Timelock.bin-runtime"

def adminSlot : Nat := 0
def feeSlot : Nat := 1
def pendingSlot : Nat := 2
def etaSlot : Nat := 3

/-- `DELAY`: two days, in seconds. -/
def delay : Nat := 2 * 24 * 60 * 60

def admin (world : Query → Nat) : Nat := World.storage world adminSlot % U160

/-- The fee changes only when a queued change is applied after its delay: the new fee is
    the queued one, and the queue is emptied. -/
theorem fee_changes_only_when_due (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Timelock env world 3000).onSuccess (fun f =>
      f.sload world feeSlot ≠ World.storage world feeSlot →
        World.storage world etaSlot ≠ 0 ∧ World.storage world etaSlot ≤ env.block.timestamp ∧
        f.sload world feeSlot = World.storage world pendingSlot ∧
        f.sload world etaSlot = 0) := by
  blaster

/-- Only the admin puts a change in the queue: anyone else can at most empty it (by
    applying the change). -/
theorem only_admin_queues (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Timelock env world 3000).onSuccess (fun f =>
      (f.sload world pendingSlot ≠ World.storage world pendingSlot ∨
        f.sload world etaSlot ≠ World.storage world etaSlot) →
      env.msg.caller = admin world ∨
        (f.sload world pendingSlot = 0 ∧ f.sload world etaSlot = 0)) := by
  blaster

/-- A change becomes executable exactly `DELAY` after it is queued, and respects the cap. -/
theorem queued_with_delay (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Timelock env world 3000).onSuccess (fun f =>
      f.sload world etaSlot ≠ World.storage world etaSlot → f.sload world etaSlot ≠ 0 →
        f.sload world etaSlot = env.block.timestamp + delay ∧
        f.sload world pendingSlot ≤ 1000) := by
  blaster

/-- The admin is fixed. -/
theorem admin_immutable (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Timelock env world 3000).onSuccess (fun f =>
      f.sload world adminSlot = World.storage world adminSlot) := by
  blaster

/-- The fee stays within the cap of 1000 basis points. -/
theorem fee_within_cap (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    World.storage world feeSlot ≤ 1000 → World.storage world pendingSlot ≤ 1000 →
    (execute Timelock env world 3000).onSuccess (fun f =>
      f.sload world feeSlot ≤ 1000 ∧ f.sload world pendingSlot ≤ 1000) := by
  blaster

/-- Liveness: once the delay has passed, anyone can apply the queued fee. -/
theorem anyone_applies_when_due (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    env.msg.calldata = .ofAbi 0xf8c8f5f8 [] → env.msg.callvalue = 0 →
    World.storage world etaSlot ≠ 0 → World.storage world etaSlot ≤ env.block.timestamp →
    (execute Timelock env world 3000).succeedsWith (fun f =>
      f.sload world feeSlot = World.storage world pendingSlot) := by
  blaster

/-! ### Sequences of calls -/

/-- A call by anyone but the admin either leaves the fee and the queue alone, or applies
    the queued change. -/
theorem call_without_admin (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → env.msg.caller ≠ admin world →
    (execute Timelock env world 3000).onSuccess (fun f =>
      (f.sload world feeSlot = World.storage world feeSlot ∧
        f.sload world pendingSlot = World.storage world pendingSlot ∧
        f.sload world etaSlot = World.storage world etaSlot) ∨
      (World.storage world etaSlot ≠ 0 ∧
        f.sload world feeSlot = World.storage world pendingSlot ∧
        f.sload world etaSlot = 0)) := by
  blaster

theorem stores_words (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Timelock env world 3000).onSuccess (fun f => ∀ k, f.sload world k < U256) := by
  blaster

theorem withStorage_WF {world : Query → Nat} {σ : Nat → Nat} :
    World.WF world → (∀ k, σ k < U256) → World.WF (World.withStorage world σ) := by
  intro hw hσ q
  cases q <;> first | exact hσ _ | exact hw _

/-- The storage reached from `σ₀` without the admin: either nothing changed, or the
    change queued in `σ₀` was applied and the queue is empty. -/
def Reachable (σ₀ τ : Nat → Nat) : Prop :=
  (τ feeSlot = σ₀ feeSlot ∧ τ pendingSlot = σ₀ pendingSlot ∧ τ etaSlot = σ₀ etaSlot) ∨
  (τ feeSlot = σ₀ pendingSlot ∧ σ₀ etaSlot ≠ 0 ∧ τ etaSlot = 0)

theorem reachable_without_admin (txs : List (Env × (Query → Nat))) (σ₀ τ : Nat → Nat) :
    (∀ k, τ k < U256) → τ adminSlot = σ₀ adminSlot → Reachable σ₀ τ →
    (∀ tx ∈ txs, tx.1.WF ∧ World.WF tx.2 ∧ tx.1.msg.caller ≠ σ₀ adminSlot % U160) →
    Reachable σ₀ (runCalls Timelock 3000 τ txs) := by
  induction txs generalizing τ with
  | nil => intro _ _ h _; exact h
  | cons tx rest ih =>
    obtain ⟨env, world⟩ := tx
    intro hτ hadmin hreach hall
    obtain ⟨henv, hworld, hcaller⟩ := hall (env, world) (by simp)
    have hrest : ∀ tx ∈ rest, tx.1.WF ∧ World.WF tx.2 ∧ tx.1.msg.caller ≠ σ₀ adminSlot % U160 :=
      fun tx htx => hall tx (by simp [htx])
    have hw := withStorage_WF hworld hτ
    -- the call's world has storage `τ`
    have hs : World.storage (World.withStorage world τ) = τ := funext fun _ => rfl
    have hc : env.msg.caller ≠ admin (World.withStorage world τ) := by
      simp only [admin, hs, hadmin]; exact hcaller
    have hcall := call_without_admin env _ henv hw hc
    have hadm := admin_immutable env _ henv hw
    have hwords := stores_words env _ henv hw
    simp only [runCalls]
    generalize execute Timelock env (World.withStorage world τ) 3000 = r at hcall hadm hwords ⊢
    cases r with
    | success f out =>
      simp only [Result.onSuccess, Frame.sload, hs] at hcall hadm hwords
      simp only [Result.storageAfter]
      apply ih _ hwords (hadm.trans hadmin) _ hrest
      unfold Reachable at hreach ⊢
      rcases hcall with ⟨e1, e2, e3⟩ | ⟨n, e1, e3⟩ <;> rcases hreach with ⟨r1, r2, r3⟩ | ⟨r1, r2, r3⟩
      · exact Or.inl ⟨e1.trans r1, e2.trans r2, e3.trans r3⟩
      · exact Or.inr ⟨e1.trans r1, r2, e3.trans r3⟩
      · exact Or.inr ⟨e1.trans r2, r3 ▸ n, e3⟩
      · exact absurd r3 n
    | revert _ | exception => exact ih τ hτ hadmin hreach hrest
    | unsupported _ | outOfFuel => exact hcall.elim

/-- Over any sequence of calls in which the admin makes no call, the fee either keeps its
    value or takes the value that was already queued at the start: users are never
    surprised by a change they could not see coming. -/
theorem fee_without_admin (txs : List (Env × (Query → Nat))) (σ : Nat → Nat) :
    (∀ k, σ k < U256) →
    (∀ tx ∈ txs, tx.1.WF ∧ World.WF tx.2 ∧ tx.1.msg.caller ≠ σ adminSlot % U160) →
    runCalls Timelock 3000 σ txs feeSlot = σ feeSlot ∨
      (runCalls Timelock 3000 σ txs feeSlot = σ pendingSlot ∧ σ etaSlot ≠ 0) := by
  intro hσ hall
  rcases reachable_without_admin txs σ σ hσ rfl (Or.inl ⟨rfl, rfl, rfl⟩) hall with
    ⟨h, _, _⟩ | ⟨h, h', _⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, h'⟩

end Examples.Timelock
