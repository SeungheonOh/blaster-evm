import EvmBlaster
import Blaster

/-!
# Codegen: a fixed loop over a storage array

`tests/contracts/Loop.sol`: `fill(x)` sets `table[i] = x * i` for `i < 4` with checked
multiplication.
-/

namespace Tests.Codegen.Loop
open Evm

#evm_contract_file Loop "tests/contracts/build/Loop.bin-runtime"

theorem fill (env : Env) (world : Query → Nat) (x : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x3fda5389 [x] →
    env.msg.callvalue = 0 →
    (3 * x < 2 ^ 256 → (execute Loop env world 1000).succeedsWith (fun f =>
      f.sload world 0 = 0 ∧ f.sload world 1 = x ∧ f.sload world 2 = 2 * x ∧
      f.sload world 3 = 3 * x)) ∧
    (2 ^ 256 ≤ 3 * x → (execute Loop env world 1000).isFailure) := by
  blaster

end Tests.Codegen.Loop
