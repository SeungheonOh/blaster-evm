import EvmBlaster
import Blaster

/-!
# Symbolic suite: machine semantics for all inputs

Small artificial programs, executed symbolically by Blaster. Each theorem states an exact
fact about the machine for *every* calldata, environment and world: arithmetic wrap-around,
byte-precise memory, copies, storage aliasing, computed jumps, hashing, calls. The
`#blaster (solve-result: 1)` commands are deliberately false claims that Blaster must refute
with a counterexample.

Programs are hand-assembled; `cd[o]` is `CALLDATALOAD o`, and calldata is
`Calldata.ofAbi 0 [x, y, ...]`, so `cd[4] = x`, `cd[36] = y`, `cd[68] = z`, `cd[100] = w`.
The shape of the calldata is stated before `env.WF`, so that the well-formedness
assumptions are about `x`, `y`, ... directly (Blaster uses the bounds they give).
-/

namespace Tests.Symbolic
open Evm

/-- Shorthand: the program's first returned word, for calldata `ofAbi 0 args`. -/
def ret (c : Contract) (env : Env) (world : Query → Nat) : Option Nat :=
  returnWord c env world (execute c env world 500)

-- cd[4] + cd[36]
#evm_contract Add "6004 35 6024 35 01 5f 52 6020 5f f3"
-- cd[36] + cd[4]
#evm_contract AddSwapped "6024 35 6004 35 01 5f 52 6020 5f f3"

/-- `ADD` wraps modulo `2^256`. -/
theorem add_wraps (env : Env) (world : Query → Nat) (x y : Nat) :
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret Add env world = some ((x + y) % 2 ^ 256) := by
  blaster

/-- Two programs computing `x + y` and `y + x` agree on every input. -/
theorem add_programs_equivalent (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    ret Add env world = ret AddSwapped env world := by
  blaster

-- (cd[4] - cd[36]) + cd[36]
#evm_contract SubAdd "6024 35 6004 35 03 6024 35 01 5f 52 6020 5f f3"

/-- Subtraction and addition are inverse modulo `2^256`, overflow included. -/
theorem sub_add_cancel (env : Env) (world : Query → Nat) (x y : Nat) :
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret SubAdd env world = some x := by
  blaster

-- MSTORE cd[4] at 0, MSTORE cd[36] at 32, MLOAD 16
#evm_contract Straddle "6004 35 5f 52 6024 35 6020 52 6010 51 5f 52 6020 5f f3"

/-- A word read across two stored words takes the low half of the first and the high half
    of the second (byte-precise memory, symbolically). -/
theorem mload_straddles (env : Env) (world : Query → Nat) (x y : Nat) :
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret Straddle env world = some ((x % 2 ^ 128) * 2 ^ 128 + y / 2 ^ 128) := by
  blaster

-- MSTORE cd[4] at 0, MSTORE8 cd[36] at 5, MLOAD 0
#evm_contract Patch "6004 35 5f 52 6024 35 6005 53 5f 51 5f 52 6020 5f f3"

/-- `MSTORE8` replaces exactly one byte: bytes 0 to 4 of `x`, then the new byte, then
    bytes 6 to 31 of `x`. -/
theorem mstore8_patches_one_byte (env : Env) (world : Query → Nat) (x y : Nat) :
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret Patch env world =
      some ((x / 2 ^ 216) * 2 ^ 216 + (y % 256) * 2 ^ 208 + x % 2 ^ 208) := by
  blaster

-- CALLDATACOPY 32 bytes from offset 4 to 0, MLOAD 0
#evm_contract CopyAligned "6020 6004 5f 37 5f 51 5f 52 6020 5f f3"
-- CALLDATACOPY 32 bytes from offset 5 to 0, MLOAD 0
#evm_contract CopyShifted "6020 6005 5f 37 5f 51 5f 52 6020 5f f3"

/-- Copying calldata to memory and loading it back is `CALLDATALOAD`. -/
theorem calldatacopy_aligned (env : Env) (world : Query → Nat) (x y : Nat) :
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret CopyAligned env world = some x := by
  blaster

theorem calldatacopy_shifted (env : Env) (world : Query → Nat) (x y : Nat) :
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret CopyShifted env world = some ((x % 2 ^ 248) * 256 + y / 2 ^ 248) := by
  blaster

-- SSTORE(cd[4], cd[36]); SSTORE(cd[68], cd[100]); SLOAD(cd[4])
#evm_contract Alias "6024 35 6004 35 55 6064 35 6044 35 55 6004 35 54 5f 52 6020 5f f3"

/-- Storage writes at symbolic keys alias exactly when the keys are equal. -/
theorem storage_aliasing (env : Env) (world : Query → Nat) (k1 v1 k2 v2 : Nat) :
    env.msg.calldata = .ofAbi 0 [k1, v1, k2, v2] → env.WF → World.WF world →
    ret Alias env world = some (if k1 = k2 then v2 else v1) := by
  blaster

-- JUMP to cd[4]; the only JUMPDEST is at 10
#evm_contract Computed "6004 35 56 fe fe fe fe fe fe 5b 00"

/-- A computed jump succeeds exactly when it lands on the `JUMPDEST`; any other target is an
    exceptional halt (never an unsupported or out-of-fuel state). -/
theorem computed_jump (env : Env) (world : Query → Nat) (x : Nat) :
    env.msg.calldata = .ofAbi 0 [x] → env.WF → World.WF world →
    ((execute Computed env world 50).isSuccess ↔ x = 10) ∧
    (x ≠ 10 → (execute Computed env world 50).isFailure) := by
  blaster

-- MSTORE cd[4] at 0, KECCAK256(0, 32)
#evm_contract Hash "6004 35 5f 52 6020 5f 20 5f 52 6020 5f f3"

/-- `KECCAK256` asks the world for the hash of the exact bytes in memory. -/
theorem keccak_query (env : Env) (world : Query → Nat) (x : Nat) :
    env.msg.calldata = .ofAbi 0 [x] → env.WF → World.WF world →
    ret Hash env world = some (world (.keccak 32 [x])) := by
  blaster

-- CALL(GAS, cd[4], cd[36], 0, 0, 0, 0); return [success, SELFBALANCE]
#evm_contract Pay "5f 5f 5f 5f 6024 35 6004 35 5a f1 5f 52 47 6020 52 6040 5f f3"

/-- A value transfer succeeds iff the contract can afford it and the world accepts the call;
    the balance moves accordingly. -/
theorem call_moves_value (env : Env) (world : Query → Nat) (to v : Nat) :
    env.msg.calldata = .ofAbi 0 [to, v] → env.WF → World.WF world →
    env.msg.callvalue = 0 → to % 2 ^ 160 ≠ env.msg.address →
    let ok := v ≤ env.balance ∧ world (.callSuccess 0) ≠ 0
    returnWord Pay env world (execute Pay env world 100) 0 = some (if ok then 1 else 0) ∧
    returnWord Pay env world (execute Pay env world 100) 1 =
      some (if ok then env.balance - v else env.balance) := by
  blaster

-- ADD on an empty stack
#evm_contract Underflow "01"
-- CREATE
#evm_contract Creates "5f 5f 5f f0"
-- JUMPDEST; PUSH0; JUMP (an infinite loop)
#evm_contract Spin "5b 5f 56"

theorem underflow_fails (env : Env) (world : Query → Nat) :
    (execute Underflow env world 10).isFailure := by
  blaster

/-- Instructions outside the model halt in `unsupported`, which no property accepts. -/
theorem create_unsupported (env : Env) (world : Query → Nat) :
    execute Creates env world 10 = .unsupported .create ∧
    ¬ (execute Creates env world 10).onSuccess (fun _ => True) := by
  blaster

/-- Running out of fuel is reported, and no property accepts it either. -/
theorem spin_out_of_fuel (env : Env) (world : Query → Nat) :
    execute Spin env world 60 = .outOfFuel := by
  blaster

/-! ## Claims Blaster must refute -/

-- cd[4] SDIV cd[36]
#evm_contract SDiv "6024 35 6004 35 05 5f 52 6020 5f f3"

-- `SDIV` is not `DIV` (negative operands).
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (x y : Nat),
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret SDiv env world = some (x / y)]

-- Memory is not word-addressed: the straddling read is not the first word.
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (x y : Nat),
    env.msg.calldata = .ofAbi 0 [x, y] → env.WF → World.WF world →
    ret Straddle env world = some x]

-- Writes at different symbolic keys may alias.
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (k1 v1 k2 v2 : Nat),
    env.msg.calldata = .ofAbi 0 [k1, v1, k2, v2] → env.WF → World.WF world →
    ret Alias env world = some v1]

-- The call may fail even when affordable: the world decides.
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (to v : Nat),
    env.msg.calldata = .ofAbi 0 [to, v] → env.WF → World.WF world → v ≤ env.balance →
    returnWord Pay env world (execute Pay env world 100) 0 = some 1]

end Tests.Symbolic
