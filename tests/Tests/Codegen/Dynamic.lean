import EvmBlaster
import Blaster

/-!
# Codegen: dynamic calldata arrays and loops

`tests/contracts/Dynamic.sol`: `sum(uint256[] xs)` decodes an offset/length header and
sums the elements with checked additions. The array length comes from calldata, so the
loop bound is symbolic unless the calldata fixes it.
-/

namespace Tests.Codegen.Dynamic
open Evm

#evm_contract_file Dynamic "tests/contracts/build/Dynamic.bin-runtime"

def out (env : Env) (world : Query → Nat) : Option Nat :=
  returnWord Dynamic env world (execute Dynamic env world 2000)

/-- A well-formed three-element array: the result is the sum, and the call reverts exactly
    when the sum overflows. -/
theorem sum_three (env : Env) (world : Query → Nat) (a b c : Nat) :
    env.WF → World.WF world → env.msg.callvalue = 0 →
    env.msg.calldata = .ofAbi 0x0194db8e [0x20, 3, a, b, c] →
    (a + b + c < 2 ^ 256 → out env world = some (a + b + c)) ∧
    (2 ^ 256 ≤ a + b + c → out env world = none) := by
  blaster

/-- A length that the calldata cannot hold is rejected before the loop runs, whatever
    the elements. -/
theorem sum_length_out_of_bounds (env : Env) (world : Query → Nat) (n a b c : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x0194db8e [0x20, n, a, b, c] →
    3 < n → n < 2 ^ 64 →
    (execute Dynamic env world 2000).isFailure := by
  blaster

/-- A length up to three, chosen by the caller: the loop runs at most three times (the
    longer paths are infeasible), and the result is the sum of the prefix. -/
theorem sum_prefix (env : Env) (world : Query → Nat) (n a b c : Nat) :
    env.WF → World.WF world → env.msg.callvalue = 0 →
    env.msg.calldata = .ofAbi 0x0194db8e [0x20, n, a, b, c] → n ≤ 3 →
    a < 2 ^ 64 → b < 2 ^ 64 → c < 2 ^ 64 →
    out env world =
      some (if n = 0 then 0 else if n = 1 then a else if n = 2 then a + b else a + b + c) := by
  blaster

end Tests.Codegen.Dynamic
