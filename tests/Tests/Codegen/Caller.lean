import EvmBlaster
import Blaster

/-!
# Codegen: calling another contract

`tests/contracts/Caller.sol`: `pay(token, to, amount)` calls `token.transfer(to, amount)`
and reverts unless it returns `true`. The callee is answered by the world, so the theorems
describe what the caller accepts from *any* token.
-/

namespace Tests.Codegen.Caller
open Evm

#evm_contract_file Caller "tests/contracts/build/Caller.bin-runtime"

/-- The word at byte `k` of a call's input. -/
def inputWordAt (env : Env) (world : Query → Nat) (c : CallRecord) (k : Nat) : Nat :=
  Memory.load (memCtx Caller env world) c.input.mem (c.input.off + k)

/-- A successful `pay` made exactly one call: to `token`, with no value, with the ABI
    encoding of `transfer(to, amount)` as input; and the token reported success and returned
    `true`. -/
theorem pay (env : Env) (world : Query → Nat) (token to amount : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0xb3d76188 [token, to, amount] →
    (execute Caller env world 1000).onSuccess (fun f =>
      OnlyCall (fun c => c.to = token ∧ c.value = 0 ∧ c.success = true ∧
        inputWordAt env world c 0 / 2 ^ 224 = 0xa9059cbb ∧
        inputWordAt env world c 4 = to ∧ inputWordAt env world c 36 = amount) f.calls ∧
      world (.returnWord 0 0) = 1) := by
  blaster

/-- A token that reports success but returns `false` makes `pay` revert. -/
theorem pay_rejects_false (env : Env) (world : Query → Nat) (token to amount : Nat) :
    env.WF → World.WF world → env.msg.calldata = .ofAbi 0xb3d76188 [token, to, amount] →
    world (.returnSize 0) = 32 → world (.returnWord 0 0) = 0 →
    (execute Caller env world 1000).isFailure := by
  blaster

end Tests.Codegen.Caller
