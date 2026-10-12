import EvmBlaster
import Blaster

/-!
# `MultiSig`: a 2-of-3 wallet

`contracts/MultiSig.sol`: owners (slots 0, 1, 2), `transactionCount` (slot 3),
`transactions` (mapping at slot 4 to a 4-slot struct: `to`, `value`, `executed`,
`numConfirmations`), `isConfirmed` (nested mapping at slot 5). Owners submit payments and
confirm them; a payment with two confirmations can be executed once, by anyone.

The struct of transaction `id` occupies the slots `keccak(id ‖ 4) + k` for `k < 4`.
Properties that relate these slots to other hashed slots rely on
`World.KeccakSpread world 4`: hashes of distinct inputs are at least 4 apart, so struct
fields never meet another mapping entry. This is the idealisation Solidity's storage
layout itself relies on.

The main result, `payments_confirmed_by_two_owners`, holds for any sequence of
transactions from a freshly deployed wallet: every payment was confirmed by two distinct
owners.
-/

namespace Examples.MultiSig
open Evm

#evm_contract_file MultiSig "contracts/build/MultiSig.bin-runtime"

/-- A keccak256 function, as the world answers it. -/
def kec (world : Query → Nat) (n : Nat) (ws : List Nat) : Nat := world (.keccak n ws)

/-- Slot `k` of `transactions[id]` (0: `to`, 1: `value`, 2: `executed`, 3:
    `numConfirmations`). -/
def txSlot (H : Nat → List Nat → Nat) (id k : Nat) : Nat := (H 64 [id, 4] + k) % U256

/-- The slot of `isConfirmed[id][a]`. -/
def confSlot (H : Nat → List Nat → Nat) (id a : Nat) : Nat := H 64 [a, H 64 [id, 5]]

/-- The `i`-th owner in storage `s`. -/
def owner (s : Nat → Nat) (i : Nat) : Nat := s i % U160

/-- A boolean in the low byte of a slot, as `0` or `1`. -/
def bit (v : Nat) : Nat := if v % 256 = 0 then 0 else 1

/-- The number of owners who confirmed transaction `id` in storage `s`. -/
def confirmations (H : Nat → List Nat → Nat) (s : Nat → Nat) (id : Nat) : Nat :=
  bit (s (confSlot H id (owner s 0))) + bit (s (confSlot H id (owner s 1)))
    + bit (s (confSlot H id (owner s 2)))

/-- The bookkeeping invariant of transaction `id`: its confirmation counter is the number
    of owners who confirmed it, and a transaction not yet submitted has none. -/
def Counted (H : Nat → List Nat → Nat) (s : Nat → Nat) (id : Nat) : Prop :=
  s (txSlot H id 3) = confirmations H s id ∧ (s 3 ≤ id → confirmations H s id = 0)

/-- The three owners are distinct addresses. (The constructor does not check it.) -/
def DistinctOwners (s : Nat → Nat) : Prop :=
  owner s 0 ≠ owner s 1 ∧ owner s 0 ≠ owner s 2 ∧ owner s 1 ≠ owner s 2

/-! ### Single calls -/

/-- Ether leaves only through `execute`. -/
theorem calls_only_by_execute (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute MultiSig env world 3000).onSuccess (fun f =>
      f.calls = [] ∨ env.msg.calldata.selector = 0xfe0d94c1) := by
  blaster

/-- `execute(id)` makes exactly one payment: to the recorded recipient, of the recorded
    value, for a submitted transaction not yet executed and with at least two recorded
    confirmations, and marks it executed. -/
theorem execute_pays_recorded (env : Env) (world : Query → Nat) (id : Nat) :
    env.msg.calldata = .ofAbi 0xfe0d94c1 [id] → env.WF → World.WF world →
    let s := World.storage world
    (execute MultiSig env world 3000).onSuccess (fun f =>
      OnlyCall (fun c => c.to = s (txSlot (kec world) id 0) % U160 ∧
        c.value = s (txSlot (kec world) id 1)) f.calls ∧
      id < s 3 ∧ s (txSlot (kec world) id 2) % 256 = 0 ∧ 2 ≤ s (txSlot (kec world) id 3) ∧
      f.sload world (txSlot (kec world) id 2) % 256 ≠ 0) := by
  blaster

/-- The owners are fixed. -/
theorem owners_immutable (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 → World.KeccakSpread world 4 →
    (execute MultiSig env world 3000).onSuccess (fun f =>
      f.sload world 0 = World.storage world 0 ∧ f.sload world 1 = World.storage world 1 ∧
      f.sload world 2 = World.storage world 2) := by
  blaster

/-- Only an owner confirms, only for themselves, and only a submitted transaction. -/
theorem only_owners_confirm (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    World.KeccakInjective world → World.KeccakAbove world 6 → World.KeccakSpread world 4 →
    let s := World.storage world
    (execute MultiSig env world 3000).onSuccess (fun f =>
      ∀ id a, a < U160 → s (confSlot (kec world) id a) % 256 = 0 →
        f.sload world (confSlot (kec world) id a) % 256 ≠ 0 →
        a = env.msg.caller ∧ (a = owner s 0 ∨ a = owner s 1 ∨ a = owner s 2) ∧ id < s 3) := by
  blaster

/-- An executed transaction stays executed. (Only submitted transactions, `id <
    transactionCount`, are ever executed; `submit` writes a fresh struct at index
    `transactionCount`.) -/
theorem executed_is_final (env : Env) (world : Query → Nat) (id : Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 → World.KeccakSpread world 4 →
    World.storage world (txSlot (kec world) id 2) % 256 ≠ 0 → id < World.storage world 3 →
    (execute MultiSig env world 3000).onSuccess (fun f =>
      f.sload world (txSlot (kec world) id 2) % 256 ≠ 0) := by
  blaster

/-- Every call keeps the confirmation counter of every transaction exact. -/
theorem counted_preserved (env : Env) (world : Query → Nat) (id : Nat) :
    env.WF → World.WF world →
    World.KeccakInjective world → World.KeccakAbove world 6 → World.KeccakSpread world 4 →
    DistinctOwners (World.storage world) → Counted (kec world) (World.storage world) id →
    (execute MultiSig env world 3000).onSuccess (fun f =>
      Counted (kec world) (f.sload world) id) := by
  blaster

/-- With exact counters, a payment needs two distinct owners' confirmations. -/
theorem execute_needs_two_owners (env : Env) (world : Query → Nat) (id : Nat) :
    env.msg.calldata = .ofAbi 0xfe0d94c1 [id] → env.WF → World.WF world →
    Counted (kec world) (World.storage world) id →
    (execute MultiSig env world 3000).onSuccess (fun _ =>
      2 ≤ confirmations (kec world) (World.storage world) id) := by
  blaster

theorem stores_words (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute MultiSig env world 3000).onSuccess (fun f => ∀ k, f.sload world k < U256) := by
  blaster

/-! ### Sequences of calls -/

theorem withStorage_WF {world : Query → Nat} {σ : Nat → Nat} :
    World.WF world → (∀ k, σ k < U256) → World.WF (World.withStorage world σ) := by
  intro hw hσ q
  cases q <;> first | exact hσ _ | exact hw _

/-- What every call of a sequence assumes about its chain state: words, the keccak
    assumptions, and one and the same keccak256 function `H` throughout. -/
def CallOK (H : Nat → List Nat → Nat) (tx : Env × (Query → Nat)) : Prop :=
  tx.1.WF ∧ World.WF tx.2 ∧ kec tx.2 = H ∧
  World.KeccakInjective tx.2 ∧ World.KeccakAbove tx.2 6 ∧ World.KeccakSpread tx.2 4

/-- Exact counters, distinct owners and well-formed storage survive any sequence of
    calls. -/
theorem counted_after_calls (H : Nat → List Nat → Nat) (id : Nat)
    (txs : List (Env × (Query → Nat))) (σ : Nat → Nat) :
    (∀ k, σ k < U256) → DistinctOwners σ → Counted H σ id → (∀ tx ∈ txs, CallOK H tx) →
    Counted H (runCalls MultiSig 3000 σ txs) id ∧
      DistinctOwners (runCalls MultiSig 3000 σ txs) ∧
      ∀ k, runCalls MultiSig 3000 σ txs k < U256 := by
  induction txs generalizing σ with
  | nil => intro hσ hd hc _; exact ⟨hc, hd, hσ⟩
  | cons tx rest ih =>
    obtain ⟨env, world⟩ := tx
    intro hσ hd hc hall
    obtain ⟨henv, hworld, hH, hinj, habove, hspread⟩ := hall (env, world) (by simp)
    have hrest : ∀ tx ∈ rest, CallOK H tx := fun tx htx => hall tx (by simp [htx])
    have hw := withStorage_WF hworld hσ
    -- the call's world has storage `σ` and keccak `H`
    have hk : kec (World.withStorage world σ) = H := hH
    have hcount := counted_preserved env _ id henv hw hinj habove hspread hd
      (by rw [hk]; exact hc)
    have howners := owners_immutable env _ henv hw habove hspread
    have hwords := stores_words env _ henv hw
    simp only [runCalls]
    generalize execute MultiSig env (World.withStorage world σ) 3000 = r at hcount howners hwords ⊢
    cases r with
    | success f out =>
      simp only [Result.onSuccess] at hcount howners hwords
      rw [hk] at hcount
      simp only [Result.storageAfter]
      obtain ⟨e0, e1, e2⟩ := howners
      have e0 : Storage.read σ f.storage 0 = σ 0 := e0
      have e1 : Storage.read σ f.storage 1 = σ 1 := e1
      have e2 : Storage.read σ f.storage 2 = σ 2 := e2
      have hd' : DistinctOwners (Storage.read σ f.storage) := by
        simp only [DistinctOwners, owner, e0, e1, e2]; exact hd
      exact ih _ hwords hd' hcount hrest
    | revert _ | exception => exact ih σ hσ hd hc hrest
    | unsupported _ | outOfFuel => exact hcount.elim

/-- A freshly deployed wallet (nothing submitted or confirmed) has exact counters. -/
theorem fresh_counted (H : Nat → List Nat → Nat) (σ : Nat → Nat) (id : Nat) :
    σ 3 = 0 → (∀ a, σ (confSlot H id a) = 0) → σ (txSlot H id 3) = 0 → Counted H σ id := by
  intro h3 hconf htx
  simp [Counted, confirmations, bit, hconf, htx]

/-- **Every payment is confirmed by two distinct owners.** Start from a freshly deployed
    wallet with three distinct owners, run any sequence of calls, then call
    `execute(id)`: if it succeeds (it pays), at least two of the three owners had
    confirmed transaction `id`. -/
theorem payments_confirmed_by_two_owners (H : Nat → List Nat → Nat) (id : Nat)
    (txs : List (Env × (Query → Nat))) (σ : Nat → Nat) (env : Env) (world : Query → Nat) :
    (∀ k, σ k < U256) → DistinctOwners σ →
    σ 3 = 0 → (∀ a, σ (confSlot H id a) = 0) → σ (txSlot H id 3) = 0 →
    (∀ tx ∈ txs, CallOK H tx) →
    env.msg.calldata = .ofAbi 0xfe0d94c1 [id] → CallOK H (env, world) →
    DistinctOwners (runCalls MultiSig 3000 σ txs) ∧
    (execute MultiSig env (World.withStorage world (runCalls MultiSig 3000 σ txs)) 3000).onSuccess
      (fun _ => 2 ≤ confirmations H (runCalls MultiSig 3000 σ txs) id) := by
  intro hσ hd h3 hconf htx hall hcd hok
  obtain ⟨hc, hd', hwords⟩ :=
    counted_after_calls H id txs σ hσ hd (fresh_counted H σ id h3 hconf htx) hall
  refine ⟨hd', ?_⟩
  obtain ⟨henv, hworld, hH, -, -, -⟩ := hok
  have hk : kec (World.withStorage world (runCalls MultiSig 3000 σ txs)) = H := hH
  have h := execute_needs_two_owners env _ id hcd henv (withStorage_WF hworld hwords)
    (by rw [hk]; exact hc)
  rw [hk] at h
  exact h

end Examples.MultiSig
