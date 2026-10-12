import EvmBlaster
import Blaster

/-!
# Codegen: signed arithmetic

`tests/contracts/Signed.sol`: two's complement comparisons, `int128` argument validation
(sign extension), checked signed addition, truncating signed division.
-/

namespace Tests.Codegen.Signed
open Evm

#evm_contract_file Signed "tests/contracts/build/Signed.bin-runtime"

/-- The first returned word, if the call succeeds. -/
def out (env : Env) (world : Query → Nat) : Option Nat :=
  returnWord Signed env world (execute Signed env world 1000)

/-- `clamp(x, lo, hi)` lands in `[lo, hi]` (as signed integers). -/
theorem clamp_in_range (env : Env) (world : Query → Nat) (x lo hi r : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x7b8d0f0c [x, lo, hi] →
    out env world = some r →
    Word.toInt lo ≤ Word.toInt r ∧ Word.toInt r ≤ Word.toInt hi := by
  blaster

/-- `avg(a, b)` reverts exactly when `a + b` overflows `int256`, and otherwise returns
    `(a + b) / 2` rounded towards zero. -/
theorem avg (env : Env) (world : Query → Nat) (a b : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0xebf274be [a, b] →
    env.msg.callvalue = 0 →
    let s := Word.toInt a + Word.toInt b
    (out env world = none ↔ (s < -2 ^ 255 ∨ 2 ^ 255 ≤ s)) ∧
    (-2 ^ 255 ≤ s → s < 2 ^ 255 → out env world = some (Word.ofInt (s.tdiv 2))) := by
  blaster

-- Blaster proves it quickly; Lean's own check of the declaration afterwards needs more
-- than the default heartbeats.
set_option maxHeartbeats 0 in
/-- `absDiff` is symmetric: the two orders of the arguments give the same result. -/
theorem absDiff_symmetric (env : Env) (world : Query → Nat) (a b : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x850e3dc3 [a, b] →
    out env world = out (env.withCalldata (.ofAbi 0x850e3dc3 [b, a])) world := by
  blaster

/-- An `int128` argument that is not a sign-extended 128-bit value is rejected. -/
theorem absDiff_rejects_dirty (env : Env) (world : Query → Nat) (a b : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x850e3dc3 [a, b] →
    Word.signextend 15 a ≠ a →
    out env world = none := by
  blaster

end Tests.Codegen.Signed
