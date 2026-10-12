import Conformance.Gas

/-!
# Conformance: running the machine on a fixture

The runner iterates the machine's own `Evm.step`, exactly as `Evm.run` does, and adds up
the gas lower bound of `Conformance.Gas` before each instruction (the EVM charges gas
before executing). It stops early when the bound exceeds the gas available: the EVM ran
out of gas on that execution. Since every instruction except the halting ones costs at
least one gas unit, every run terminates.
-/

namespace Conformance
open Evm

/-- How a run ended. -/
inductive Ending where
  | halted (r : Result)
  /-- The gas bound exceeded the gas available before the instruction at `pc`. -/
  | outOfGas (pc : Nat)
deriving Inhabited

structure Run where
  ending : Ending
  /-- The last frame before the run ended (its calls, for a failed execution). -/
  last : Frame
  steps : Nat
  /-- Whether the execution read `GAS`, whose value the machine leaves to the world. -/
  readsGas : Bool
deriving Inhabited

partial def drive (c : Contract) (env : Env) (world : Query → Nat) (g : GasCtx)
    (gasAvail : Nat) (f : Frame) (w : Warm) (steps used : Nat) (readsGas : Bool) : Run :=
  let i? := c.code.fetch f.pc
  let ch := (i?.map (charge g w f)).getD ⟨0, 0, w⟩
  if gasAvail < used + ch.required then
    { ending := .outOfGas f.pc, last := f, steps, readsGas }
  else
    let readsGas := readsGas || i? == some (.ctx .gas)
    match step c env world f with
    | .halted r => { ending := .halted r, last := f, steps := steps + 1, readsGas }
    | .running _ _ _ f' => drive c env world g gasAvail f' ch.warm (steps + 1) (used + ch.net) readsGas

/-- Run a message call from its initial frame, with the accounts and slots `warm` at the
    start (EIP-2929). -/
def runCall (c : Contract) (env : Env) (world : Query → Nat) (g : GasCtx) (gasAvail : Nat)
    (warm : Warm := {}) : Run :=
  drive c env world g gasAvail (Frame.init env) warm 0 0 false

/-- The storage after a successful execution: the initial storage with the frame's
    writes, read back with the machine's own `Storage.read`. -/
def storageAfter (init : Std.HashMap Nat Nat) (f : Frame) : Std.HashMap Nat Nat :=
  let read := Storage.read (fun k => init.getD k 0) f.storage
  (f.storage.map (·.1)).foldl (fun m k => m.insert k (read k)) init

/-- The verdict on one test. -/
inductive Verdict where
  /-- The machine's results agree with the expected ones. -/
  | pass
  /-- The expected result is an exceptional halt, and the machine's execution exceeds the
      gas available by the lower bound: it ran out of gas in the EVM. -/
  | passOutOfGas
  /-- A difference explained by gas (the execution reads `GAS`). -/
  | inconclusive (why : String)
  /-- Outside the modelled fragment (unsupported instruction, call to a contract, ...). -/
  | outOfScope (why : String)
  | fail (why : String)

def instrName (i : Instr) : String :=
  match i with
  | .callcode => "CALLCODE" | .delegatecall => "DELEGATECALL" | .create => "CREATE"
  | .create2 => "CREATE2" | .selfdestruct => "SELFDESTRUCT" | .extcodecopy => "EXTCODECOPY"
  | i => toString (repr i)

def showStorage (m : Std.HashMap Nat Nat) : String :=
  toString ((storageList m).map fun (k, v) => s!"{k}: {v}")

end Conformance
