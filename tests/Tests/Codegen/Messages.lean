import EvmBlaster
import Blaster

/-!
# Codegen: revert reasons and string returns

`tests/contracts/Messages.sol`: `require(x > 10, "too small")` reverts with the ABI
encoding of `Error("too small")`; otherwise the function returns the string `"ok"`.
-/

namespace Tests.Codegen.Messages
open Evm

#evm_contract_file Messages "tests/contracts/build/Messages.bin-runtime"

/-- The word at byte `k` of the output of a result (returned or reverted). -/
def outWordAt (env : Env) (world : Query → Nat) (k : Nat) : Result → Option Nat
  | .success _ out | .revert out => some (Memory.load (memCtx Messages env world) out.mem (out.off + k))
  | _ => none

def tooSmall : Nat := 0x746f6f20736d616c6c0000000000000000000000000000000000000000000000
def ok : Nat := 0x6f6b000000000000000000000000000000000000000000000000000000000000

/-- `check(x)` with `x ≤ 10` reverts with `Error("too small")`: selector `0x08c379a0`,
    then the offset, the length and the bytes of the string. -/
theorem reverts_with_reason (env : Env) (world : Query → Nat) (x : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x5f72f450 [x] →
    env.msg.callvalue = 0 → x ≤ 10 →
    let r := execute Messages env world 1000
    r.isFailure ∧
    outWordAt env world 0 r = some (0x08c379a0 * 2 ^ 224) ∧
    outWordAt env world 4 r = some 0x20 ∧
    outWordAt env world 36 r = some 9 ∧
    outWordAt env world 68 r = some tooSmall := by
  blaster

/-- Otherwise it returns the ABI-encoded string `"ok"`. -/
theorem returns_ok (env : Env) (world : Query → Nat) (x : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0x5f72f450 [x] →
    env.msg.callvalue = 0 → 10 < x →
    let r := execute Messages env world 1000
    r.isSuccess ∧
    outWordAt env world 0 r = some 0x20 ∧
    outWordAt env world 32 r = some 2 ∧
    outWordAt env world 64 r = some ok := by
  blaster

end Tests.Codegen.Messages
