import EvmBlaster.Env

/-!
# Solidity storage layout

Helpers to state properties in terms of Solidity state variables.
-/

namespace Evm.Solidity

/-- The slot of `m[key]` for a mapping `m` at slot `slot`: `keccak256(key ‖ slot)`. -/
def mappingSlot (world : Query → Nat) (slot key : Nat) : Nat := world (.keccak 64 [key, slot])

/-- The slot of `m[k1][k2]` for a nested mapping `m` at slot `slot`. -/
def mappingSlot2 (world : Query → Nat) (slot k1 k2 : Nat) : Nat :=
  mappingSlot world (mappingSlot world slot k1) k2

/-- A string shorter than 32 bytes as Solidity stores it: the bytes left-aligned and twice
    the length in the last byte. -/
def shortString (s : String) : Nat :=
  (s.toUTF8.foldl (fun acc b => acc * 256 + b.toNat) 0) * 2 ^ (8 * (32 - s.utf8ByteSize)) +
    2 * s.utf8ByteSize

end Evm.Solidity
