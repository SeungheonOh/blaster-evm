import EvmBlaster.Spec

/-!
# Solidity storage and effects

Helpers for stating properties at the level of Solidity: packed storage fields, mapping
and struct slots, Ether sent by a call, events emitted. Used by the UAL front end
(`UAL.Evm`); the hash assumptions are in `EvmBlaster/Hashes.lean`.
-/

namespace Evm.Sol

/-- The `n` bytes at byte offset `off` of a storage word (Solidity packs small values). -/
def field (v off n : Nat) : Nat := (v / 2 ^ (8 * off)) % 2 ^ (8 * n)

/-- The two's complement reading of an `n`-bit value. -/
def signed (bits v : Nat) : Int :=
  if v < 2 ^ (bits - 1) then Int.ofNat v else Int.ofNat v - Int.ofNat (2 ^ bits)

/-- The keccak256 slot of `m[k]` for a mapping at slot `p`. -/
def mapSlot (world : Query → Nat) (p k : Nat) : Nat := world (.keccak 64 [k, p])

/-- Slot `i` of a struct stored at `base`. -/
def structSlot (base i : Nat) : Nat := (base + i) % U256

/-- Ether sent to `a` by the successful calls among `cs`. -/
def paidTo (a : Nat) : List CallRecord → Nat
  | [] => 0
  | c :: cs => (if c.success ∧ c.to = a then c.value else 0) + paidTo a cs

/-- Ether sent by the successful calls among `cs`. -/
def sentBy : List CallRecord → Nat
  | [] => 0
  | c :: cs => (if c.success then c.value else 0) + sentBy cs

/-- Whether one of the logs has `t` as its first topic (an event signature). -/
def emittedIn (t : Nat) : List LogEntry → Bool
  | [] => false
  | l :: ls => decide (l.topics.head? = some t) || emittedIn t ls

/-- A `string` (or `bytes`) state variable holds a short value (under 32 bytes, stored in
    its slot): long values are read with a loop whose length the solver would have to
    bound. -/
def ShortString (v : Nat) : Prop := v % 2 = 0 ∧ v % 256 < 64

end Evm.Sol
