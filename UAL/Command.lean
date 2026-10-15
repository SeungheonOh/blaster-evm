import Lean
import Blaster
import UAL.Evm
import UAL.SExp

/-!
# `#ual_property`: proving a UAL property

`#ual_property name info timeout : statement [:= by tactic]` is what a UAL `PROPERTY`
annotation becomes (one per generated Lean file). The command:

1. elaborates the statement;
2. adds the assumptions of the EVM model for each `Env` and `World` it quantifies over
   (`Env.WF`, `UAL.ValidWorld info`), that the arguments of every `ONCHAIN` call are valid
   values of their Solidity types (`f.inputs`), that the keccak256 hashes the statement
   involves do not collide (`Evm.CollisionFree`, over `f.hashes` and the hashes of the
   storage reads), and the obligation that every `ONCHAIN` call it mentions stays within
   the model (`UAL.covered`);
3. runs Blaster on the result;
4. on a counterexample, instantiates the statement with the counterexample's values and
   replays every `ONCHAIN` call in it on the EVM model (`f.trace`);
5. declares the theorem when it is proved, and reports the outcome as a message
   `UAL-RESULT {json}` for the `blaster-evm` driver.

With an explicit tactic (`:= by tactic`) the statement (with the assumptions) is proved
with that tactic instead.

`#ual_check name info : statement` only elaborates the statement and adds the assumptions
(`blaster-evm check`).
-/

namespace UAL
open Lean Elab Command Term Meta

syntax (name := ualProperty) "#ual_property " ident ident num " : " term
  (" := " "by" Lean.Parser.Tactic.tacticSeq)? : command

syntax (name := ualCheck) "#ual_check " ident ident " : " term : command

unsafe def evalStringUnsafe (e : Expr) : TermElabM String :=
  Lean.Meta.evalExpr String (mkConst ``String) e

@[implemented_by evalStringUnsafe]
opaque evalString (e : Expr) : TermElabM String

unsafe def evalEnvJsonUnsafe (e : Expr) : TermElabM String :=
  Lean.Meta.evalExpr String (mkConst ``String) (mkApp (mkConst ``Evm.Replay.envJson) e)

@[implemented_by evalEnvJsonUnsafe]
opaque evalEnvJson (e : Expr) : TermElabM String

unsafe def evalInfoUnsafe (n : Name) : TermElabM ContractInfo := do
  ofExcept <| (← getEnv).evalConstCheck ContractInfo (← getOptions) ``ContractInfo n

@[implemented_by evalInfoUnsafe]
opaque evalInfo (n : Name) : TermElabM ContractInfo

def worldType : Expr := .forallE `q (mkConst ``Evm.Query) (mkConst ``Nat) .default

/-- The fully applied applications in `e`, without loose bound variables, of constants
    tagged with `attr`. -/
partial def taggedApps (attr : TagAttribute) (env : Environment) (e : Expr) (acc : Array Expr := #[]) :
    MetaM (Array Expr) := do
  let acc ← match e.getAppFn with
    | .const n _ =>
      if attr.hasTag env n && !e.hasLooseBVars then
        let arity ← forallTelescope (← getConstInfo n).type fun xs _ => pure xs.size
        pure (if e.getAppNumArgs == arity && !acc.contains e then acc.push e else acc)
      else pure acc
    | _ => pure acc
  match e with
  | .app f a => taggedApps attr env a (← taggedApps attr env f acc)
  | .lam _ t b _ | .forallE _ t b _ => taggedApps attr env b (← taggedApps attr env t acc)
  | .letE _ t v b _ => taggedApps attr env b (← taggedApps attr env v (← taggedApps attr env t acc))
  | .mdata _ b | .proj _ _ b => taggedApps attr env b acc
  | _ => pure acc

/-- The `ONCHAIN` calls in `e`. -/
def onchainCalls (env : Environment) (e : Expr) : MetaM (Array Expr) := taggedApps onchainAttr env e

/-- `(world, hash inputs)` of the calls and storage reads of `e`. -/
def hashSources (env : Environment) (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut out : Array (Expr × Expr) := #[]
  for c in ← taggedApps onchainAttr env e do
    let some f := c.getAppFn.constName? | continue
    if c.hasLooseBVars || !env.contains (f ++ `hashes) then continue
    out := out.push (c.getAppArgs.back!, mkAppN (mkConst (f ++ `hashes)) c.getAppArgs)
  for a in ← taggedApps storageAttr env e do
    let some f := a.getAppFn.constName? | continue
    if a.hasLooseBVars || !env.contains (f ++ `hashes) then continue
    -- the snapshot is the first argument; its keccak256 is the world's
    let w ← whnf (mkApp (mkConst ``UAL.Snapshot.world) a.getAppArgs[0]!)
    out := out.push (w, mkAppN (mkConst (f ++ `hashes)) a.getAppArgs)
  return out

/-- The statement with the model's assumptions: valid environments and chain states, valid
    arguments, collision-free hashes (for the hashes the statement involves). -/
def augment (info : Name) (gap : Nat) (xs : Array Expr) (body : Expr) (calls : Array Expr) :
    MetaM Expr := do
  let mut hyps : Array Expr := #[]
  for x in xs do
    let t ← inferType x
    if ← isDefEq t (mkConst ``Evm.Env) then
      hyps := hyps.push (mkApp (mkConst ``Evm.Env.WF) x)
    else if ← isDefEq t worldType then
      hyps := hyps.push (mkApp2 (mkConst ``UAL.ValidWorld) (mkConst info) x)
  -- collision freedom, per chain state, of all the hashes involved
  let mut groups : Array (Expr × Array Expr) := #[]
  for (w, l) in ← hashSources (← getEnv) body do
    match groups.findIdx? (·.1 == w) with
    | some i => groups := groups.modify i fun (w, ls) => (w, ls.push l)
    | none => groups := groups.push (w, #[l])
  let hashTy := Lean.mkConst ``Evm.HashInput
  for (w, ls) in groups do
    let nil := mkApp (mkConst ``List.nil [0]) hashTy
    let all := ls.foldr (fun l acc => mkApp3 (mkConst ``List.append [0]) hashTy l acc) nil
    hyps := hyps.push (mkApp3 (mkConst ``Evm.CollisionFree) w (mkNatLit gap) all)
  let covers := calls.filter fun c => !c.hasLooseBVars
  -- the arguments of each call are valid values of their Solidity types
  for c in covers do
    if let some f := c.getAppFn.constName? then
      let inputs := f ++ `inputs
      if (← getEnv).contains inputs then
        -- `f.inputs` takes the arguments of `f` but its environment and chain state
        hyps := hyps.push (mkAppN (mkConst inputs) (c.getAppArgs.extract 0 (c.getAppNumArgs - 2)))
  let concl := covers.foldr (fun c acc => mkAnd (mkApp (mkConst ``UAL.covered) c) acc) body
  let stmt ← hyps.foldrM (fun h acc => mkArrow h acc) concl
  mkForallFVars xs stmt

/-! ### Counterexamples -/

/-- A counterexample as Blaster prints it: values of the quantified variables, and the
    values of function variables at some arguments (and elsewhere). -/
structure Cex where
  values : List (String × String) := []
  points : List (String × String × String) := []
  defaults : List (String × String) := []

def oneLine (s : String) : String := " ".intercalate ((s.split Char.isWhitespace).filter (· ≠ ""))

def readCex (lines : List String) : Cex := Id.run do
  let mut c : Cex := {}
  for raw in lines do
    let l := oneLine raw
    if l.startsWith "(further" then continue
    match l.splitOn " (any other argument) = " with
    | [f, v] => c := { c with defaults := (f, v) :: c.defaults }; continue
    | _ => pure ()
    match l.splitOn ": " with
    | n :: rest =>
      if !n.contains ' ' && !rest.isEmpty then
        let v := ": ".intercalate rest
        if !v.startsWith "@@" then c := { c with values := (n, v) :: c.values }
        continue
    | _ => pure ()
    -- `f (arg) = value`
    match (l.splitOn " = ").reverse with
    | v :: restRev =>
      let lhs := " = ".intercalate restRev.reverse
      match lhs.splitOn " " with
      | f :: _ => c := { c with points := (f, (lhs.drop (f.length + 1)), v) :: c.points }
      | _ => pure ()
    | _ => pure ()
  return { c with points := c.points.reverse }

/-- Elaborate the Lean text of a value at type `ty`. -/
def elabValue (text : String) (ty : Expr) : TermElabM (Option Expr) := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .error _ => return none
  | .ok stx =>
    try
      let v ← Term.elabTermEnsuringType stx ty
      Term.synthesizeSyntheticMVarsNoPostponing
      let v ← instantiateMVars v
      return if v.hasMVar then none else some v
    catch _ => return none

/-- The value of quantified variable `x` in the counterexample (a default if missing). -/
def cexValue (c : Cex) (x : Expr) : TermElabM (Expr × String) := do
  let name := (← x.fvarId!.getDecl).userName.toString
  let ty ← inferType x
  let text? : Option String :=
    if ← isDefEq ty worldType then
      let pts := c.points.filter (·.1 == name)
      let d := (c.defaults.find? (·.1 == name)).map (·.2) |>.getD "0"
      some ("fun (q : Evm.Query) => " ++
        String.join (pts.map fun (_, a, v) =>
          s!"if q = {SExp.leanOfValue a} then {SExp.leanOfValue v} else ") ++ SExp.leanOfValue d)
    else (c.values.find? (·.1 == name)).map (SExp.leanOfValue ·.2)
  if let some t := text? then
    if let some v ← elabValue t ty then return (v, t)
  let d ← mkAppOptM ``Inhabited.default #[ty, none]
  return (d, "default")

/-! ### Which parts of a statement fail -/

/-- The hypotheses and the conjuncts of the conclusion of a statement body. -/
partial def splitStatement (e : Expr) : List Expr × List Expr :=
  match e with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then ([], [e]) else
    let (hs, cs) := splitStatement b
    (d :: hs, cs)
  | .mdata _ b => splitStatement b
  | _ => ([], conjuncts e)
where
  conjuncts (e : Expr) : List Expr :=
    if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg! else [e]

unsafe def evalBoolUnsafe (e : Expr) : TermElabM Bool := Lean.Meta.evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe]
opaque evalBool (e : Expr) : TermElabM Bool

/-- Whether a closed proposition holds, if it is decidable. -/
def holds? (p : Expr) : TermElabM (Option Bool) := do
  try
    let d ← mkDecide p
    return some (← evalBool (← instantiateMVars d))
  catch _ => return none

/-- The conjuncts of the conclusion of `body` (over the variables `ys`), as text, with
    whether they hold for the counterexample values `vals`. -/
def evalConclusion (body : Expr) (ys vals : Array Expr) : TermElabM (Array Json) :=
  -- the `let`s of the statement stay named (`r`) in the text
  lambdaLetTelescope body fun _ inner => do
    let (_, cs) := splitStatement inner
    let mut out : Array Json := #[]
    for c in cs do
      let v ← holds? ((← zetaReduce c).replaceFVars ys vals)
      out := out.push (Json.mkObj [("text", toString (← ppExpr c)),
        ("holds", match v with | some b => Json.bool b | none => Json.null)])
    return out

/-! ### The command -/

def runBlaster (stmt : Expr) (timeout : Nat) : TermElabM Blaster.Smt.Result := do
  let sOpts : Blaster.Options.BlasterOptions := { timeout := some timeout }
  let env := {(default : Blaster.Optimize.TranslateEnv) with optEnv.options.solverOptions := sOpts}
  let ((res, _), _) ← withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) do
    IO.setNumHeartbeats 0
    (Blaster.Smt.Translate.main stmt (logUndetermined := false)).run env
  return res

def declare (name : Name) (stmt : Expr) (value : Expr) : TermElabM Unit :=
  addDecl (.thmDecl { name, levelParams := [], type := stmt, value })

def report (fields : List (String × Json)) : TermElabM Unit :=
  logInfo m!"UAL-RESULT {(Json.mkObj fields).compress}"

@[command_elab ualProperty]
def elabUalProperty : CommandElab := fun stx => do
  let name := stx[1].getId
  let info := stx[2].getId
  let timeout := stx[3].isNatLit?.getD 120
  let bodyStx := stx[5]
  let tac? := if stx[6].getNumArgs > 0 then some stx[6][2] else none
  let declName := (← getCurrNamespace) ++ name
  liftTermElabM do
    let start ← IO.monoMsNow
    let e ← Term.elabTermEnsuringType bodyStx (mkSort .zero)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar then throwErrorAt bodyStx "the statement still has holes"
    let infoV ← evalInfo info
    let elapsed := fun () => do return Json.num ((← IO.monoMsNow) - start : Nat)
    forallTelescope e fun xs body => do
      let calls ← onchainCalls (← getEnv) body
      if let some tac := tac? then
        let stmt ← augment info (max 1 infoV.structSize) xs body calls
        let pf ← Term.elabTermEnsuringType (← `(by $(⟨tac⟩))) stmt
        Term.synthesizeSyntheticMVarsNoPostponing
        declare declName stmt (← instantiateMVars pf)
        report [("status", "proved"), ("phase", 0), ("time", ← elapsed ())]
        return
      let gap := max 1 infoV.structSize
      let stmt ← augment info gap xs body calls
      match ← runBlaster stmt timeout with
      | .Valid =>
        declare declName stmt (mkApp (mkConst ``Blaster.Tactic.blasterProven [levelZero]) stmt)
        report [("status", "proved"), ("time", ← elapsed ())]
      | .Undetermined =>
        report [("status", Json.str "unknown"), ("time", ← elapsed ()),
          ("why", Json.str s!"the solver gave up (timeout {timeout}s)")]
      | .Falsified lines =>
        let cex := readCex lines
        let mut vals : Array Expr := #[]
        let mut shown : Array Json := #[]
        let mut ys : Array Expr := #[]
        for x in xs do
          if ← isProp (← inferType x) then continue
          let (v, t) ← cexValue cex x
          ys := ys.push x
          vals := vals.push v
          let ty ← inferType x
          let mut fields : List (String × Json) := [("name", Json.str (← x.fvarId!.getDecl).userName.toString),
            ("type", Json.str (toString (← ppExpr ty))), ("value", Json.str t)]
          if ← isDefEq ty (mkConst ``Evm.Env) then
            if let .ok j := Json.parse (← evalEnvJson v) then fields := fields ++ [("env", j)]
          shown := shown.push (Json.mkObj fields)
        let body' := body.replaceFVars ys vals
        let mut callsJ : Array Json := #[]
        for c in ← onchainCalls (← getEnv) body' do
          if c.hasFVar then continue
          let some f := c.getAppFn.constName? | continue
          let t ← evalString (mkAppN (mkConst (f ++ `trace)) c.getAppArgs)
          callsJ := callsJ.push (Json.mkObj [("fn", f.toString),
            ("trace", (Json.parse t).toOption.getD Json.null)])
        let concl ← try evalConclusion body ys vals catch _ => pure #[]
        report [("status", "falsified"), ("time", ← elapsed ()), ("vars", Json.arr shown),
          ("conclusion", Json.arr concl),
          ("calls", Json.arr callsJ), ("world", Json.arr (cex.points.toArray.map fun (f, a, v) =>
            Json.mkObj [("fn", f), ("arg", SExp.leanOfValue a), ("raw", a), ("value", v)]))]

@[command_elab ualCheck]
def elabUalCheck : CommandElab := fun stx => do
  let info := stx[2].getId
  let bodyStx := stx[4]
  liftTermElabM do
    let e ← Term.elabTermEnsuringType bodyStx (mkSort .zero)
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasMVar then throwErrorAt bodyStx "the statement still has holes"
    let infoV ← evalInfo info
    forallTelescope e fun xs body => do
      let calls ← onchainCalls (← getEnv) body
      discard <| augment info (max 1 infoV.structSize) xs body calls
      report [("status", "checked"), ("name", stx[1].getId.toString), ("calls", calls.size)]

end UAL
