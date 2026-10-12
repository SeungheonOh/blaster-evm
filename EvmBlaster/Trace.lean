import EvmBlaster.Machine

/-!
# Sequences of calls

A theorem about one call quantifies over every chain state, so it also holds for each call
of any sequence. `runCalls` makes the sequence explicit: each call sees the storage left by
the previous one, while everything else (block, caller, calldata, other accounts, outcomes
of outgoing calls) comes from that call's own `env` and `world` and may change arbitrarily
between calls, e.g. because of other transactions. Properties of whole sequences then
follow from properties of single calls by induction (see `Examples.Config`).
-/

namespace Evm

/-- The contract's storage after a call from storage `σ`: the final storage if the call
    succeeded, `σ` otherwise (a revert or exceptional halt discards every write). -/
def Result.storageAfter (σ : Nat → Nat) : Result → Nat → Nat
  | .success f _ => Storage.read σ f.storage
  | _ => σ

/-- The storage of `c` after the calls `txs`, starting from storage `σ`. -/
def runCalls (c : Contract) (fuel : Nat) (σ : Nat → Nat) :
    List (Env × (Query → Nat)) → Nat → Nat
  | [] => σ
  | (env, world) :: rest =>
    runCalls c fuel ((execute c env (World.withStorage world σ) fuel).storageAfter σ) rest

end Evm
