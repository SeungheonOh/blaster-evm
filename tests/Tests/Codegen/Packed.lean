import EvmBlaster
import Blaster

/-!
# Codegen: packed storage

`tests/contracts/Packed.sol`: `owner`, `paused`, `counter` share slot 0; `lo` and `hi`
share slot 1. Every write is a masked read-modify-write; the theorems check that each one
updates exactly its own bits.
-/

namespace Tests.Codegen.Packed
open Evm

#evm_contract_file Packed "tests/contracts/build/Packed.bin-runtime"

def owner (s : Nat) : Nat := s % 2 ^ 160
def paused (s : Nat) : Nat := (s / 2 ^ 160) % 256
def counter (s : Nat) : Nat := (s / 2 ^ 168) % 2 ^ 64
def lo (s : Nat) : Nat := s % 2 ^ 128
def hi (s : Nat) : Nat := s / 2 ^ 128

abbrev slot0 (world : Query → Nat) : Nat := World.storage world 0
abbrev slot1 (world : Query → Nat) : Nat := World.storage world 1

/-- No function writes `owner`, whichever neighbour it updates. -/
theorem owner_untouched (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Packed env world 1000).onSuccess (fun f =>
      owner (f.sload world 0) = owner (slot0 world)) := by
  blaster

/-- Only the owner flips `paused`. -/
theorem only_owner_pauses (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Packed env world 1000).onSuccess (fun f =>
      paused (f.sload world 0) ≠ paused (slot0 world) → env.msg.caller = owner (slot0 world)) := by
  blaster

/-- `bump` adds exactly one to `counter`, leaves the other fields of the slot alone, and
    fails when paused or at the `uint64` maximum. -/
theorem bump (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x68110b2f [] →
    (execute Packed env world 1000).onSuccess (fun f =>
      counter (f.sload world 0) = counter (slot0 world) + 1 ∧
      paused (slot0 world) = 0 ∧
      owner (f.sload world 0) = owner (slot0 world) ∧
      paused (f.sload world 0) = paused (slot0 world)) := by
  blaster

theorem bump_overflow_reverts (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x68110b2f [] →
    counter (slot0 world) = 2 ^ 64 - 1 →
    (execute Packed env world 1000).isFailure := by
  blaster

/-- `setLo` writes `lo` and only `lo`; out-of-range arguments are rejected by the ABI
    decoder. -/
theorem setLo (env : Env) (world : Query → Nat) (v : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0xe0bb867f [v] →
    env.msg.callvalue = 0 → v < 2 ^ 128 →
    (execute Packed env world 1000).succeedsWith (fun f =>
      lo (f.sload world 1) = v ∧ hi (f.sload world 1) = hi (slot1 world)) := by
  blaster

theorem setLo_rejects_wide (env : Env) (world : Query → Nat) (v : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0xe0bb867f [v] → 2 ^ 128 ≤ v →
    (execute Packed env world 1000).isFailure := by
  blaster

/-- `setHi` writes `hi` and only `hi`. -/
theorem setHi (env : Env) (world : Query → Nat) (v : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x475ecb02 [v] →
    (execute Packed env world 1000).onSuccess (fun f =>
      hi (f.sload world 1) = v ∧ lo (f.sload world 1) = lo (slot1 world)) := by
  blaster

end Tests.Codegen.Packed
