import EvmBlaster.Machine

/-!
# Specification helpers

Properties of a contract are stated over `execute c env world fuel` for an arbitrary
environment `env` and chain state `world`. Two shapes cover most needs:

* `Result.onSuccess P`: every successful execution satisfies `P`. Reverts and exceptional
  halts discard all effects, so they satisfy every such property. Executions that leave
  the modelled fragment or exhaust the fuel do not: proving the property also proves
  that the model covers every path within the fuel bound.
* `Result.isSuccess`: the execution succeeds (used for "this call is not blocked").
-/

namespace Evm

namespace Result

def onSuccess (P : Frame → Prop) : Result → Prop
  | .success f _ => P f
  | .revert _ | .exception => True
  | .unsupported _ | .outOfFuel => False

def isSuccess : Result → Prop
  | .success .. => True
  | _ => False

/-- The execution succeeds and its final frame satisfies `P`. -/
def succeedsWith (P : Frame → Prop) : Result → Prop
  | .success f _ => P f
  | _ => False

/-- The execution ends without effect (revert or exceptional halt). -/
def isFailure : Result → Prop
  | .revert _ | .exception => True
  | _ => False

/-- The output of a successful execution. -/
def output? : Result → Option Slice
  | .success _ out => some out
  | _ => none

end Result

/-- The `i`-th word returned by a successful execution of `c`, if it succeeds. -/
def returnWord (c : Contract) (env : Env) (world : Query → Nat) (r : Result) (i : Nat := 0) :
    Option Nat :=
  match r with
  | .success _ out => some (out.word (memCtx c env world) i)
  | _ => none

namespace Frame

/-- Storage slot `k` in this frame. -/
def sload (world : Query → Nat) (f : Frame) (k : Nat) : Nat :=
  Storage.read (World.storage world) f.storage k

/-- Total value sent by successful outgoing calls. -/
def valueSent (f : Frame) : Nat := go f.calls
 where
  go : List CallRecord → Nat
  | [] => 0
  | c :: cs => (if c.success then c.value else 0) + go cs

end Frame

/-- Every outgoing call of `f` satisfies `P`. -/
def AllCalls (P : CallRecord → Prop) : List CallRecord → Prop
  | [] => True
  | c :: cs => P c ∧ AllCalls P cs

/-- Exactly one outgoing call, which satisfies `P`. (A match rather than
    `∃ c, calls = [c] ∧ P c`, which would put a quantifier in the SMT query.) -/
def OnlyCall (P : CallRecord → Prop) : List CallRecord → Prop
  | [c] => P c
  | _ => False

/-- Every log of `f` satisfies `P`. -/
def AllLogs (P : LogEntry → Prop) : List LogEntry → Prop
  | [] => True
  | l :: ls => P l ∧ AllLogs P ls

/-- The address held in the low 160 bits of a storage word. -/
def asAddress (w : Nat) : Nat := w % U160

end Evm
