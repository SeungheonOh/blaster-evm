import Lean
import UAL.Driver.Model
import UAL.Driver.Solidity

/-!
# Generating Lean

For a Solidity file `Stem.sol` the front end generates, under `UALGen.Stem_<hash>`:

* `Contracts`: per contract (namespace `C`), its bytecode, the storage accessors, the events,
  and a Lean function per `ONCHAIN` function (plus `C.dispatch`, a call to any function);
* `Predicates`: the `PREDICATE` annotations, in namespace `StemPredicates` (as UAL puts the
  predicates of module `M` in `MPredicates`);
* one file per `PROPERTY`, with its `#ual_property` command.

Annotation text is copied with its line structure, and its first line padded to its column,
so that a position in a generated file maps back to the Solidity file by a line offset
(`SourceMap`).
-/

namespace UAL.Driver
open Lean

/-! ### Writing Lean with a source map -/

/-- Generated lines `[gen, gen + count)` are the Solidity lines from `src`. -/
structure Segment where
  gen : Nat
  src : Nat
  count : Nat
deriving Inhabited

structure Writer where
  lines : Array String := #[]
  map : Array Segment := #[]

def Writer.emit (w : Writer) (s : String := "") : Writer :=
  { w with lines := w.lines ++ (s.splitOn "\n").toArray }

/-- Emit the Solidity text `src[span]`, keeping its columns. -/
def Writer.emitSpan (w : Writer) (src : String) (span : Span) : Writer :=
  let p := posOf src span.start
  let text := String.mk (List.replicate (p.col - 1) ' ') ++ src.extract span.start span.stop
  let ls := (text.splitOn "\n").toArray
  { lines := w.lines ++ ls, map := w.map.push ⟨w.lines.size + 1, p.line, ls.size⟩ }

def Writer.render (w : Writer) : String := "\n".intercalate w.lines.toList ++ "\n"

/-- The Solidity line of a generated line, if it is annotation text. -/
def locate (map : Array Segment) (line : Nat) : Option Nat :=
  map.findSome? fun s => if s.gen ≤ line && line < s.gen + s.count then some (s.src + (line - s.gen)) else none

/-! ### Names -/

def leanKeywords : List String :=
  ["at", "by", "do", "else", "end", "fun", "have", "if", "in", "let", "match", "open", "show",
   "then", "with", "where", "from", "for", "unless", "return", "mut", "try", "catch", "finally",
   "break", "continue", "def", "theorem", "lemma", "example", "abbrev", "instance", "structure",
   "class", "inductive", "namespace", "section", "variable", "universe", "import", "export",
   "calc", "Type", "Prop", "Sort", "forall", "deriving", "local", "private", "protected",
   "partial", "unsafe", "macro", "syntax", "notation", "infix", "infixl", "infixr", "prefix",
   "postfix", "attribute", "axiom", "opaque", "mutual", "noncomputable", "set_option", "nomatch",
   "nofun", "termination_by", "decreasing_by", "omit", "include", "suffices", "obtain", "this"]

def leanName (s : String) : String :=
  if leanKeywords.contains s then s!"«{s}»" else s

def sanitize (s : String) : String :=
  let t := s.map fun c => if c.isAlphanum || c == '_' then c else '_'
  if t.front.isDigit then "M" ++ t else t

/-- Text that is safe inside a Lean comment (comments nest). -/
def commentSafe (s : String) : String := (s.replace "/-" "/ -").replace "-/" "- /"

def hex (n : Nat) : String := "0x" ++ String.mk (Nat.toDigits 16 n)

/-! ### Storage accessors -/

/-- The Lean expression reading a value of type `t` from slot `slot` at byte `off`. -/
partial def valueExpr (t : SolType) (slot : String) (off : Nat) : String :=
  match t with
  | .value _ bytes lean bits =>
    let raw := if off == 0 && bytes == 32 then s!"s.storage ({slot})"
      else s!"Sol.field (s.storage ({slot})) {off} {bytes}"
    if lean == "Bool" then s!"decide ({raw} ≠ 0)"
    else if lean == "Int" then s!"Sol.signed {bits} ({raw})"
    else raw
  | .struct _ _ _ ms =>
    "⟨" ++ ", ".intercalate (ms.map fun (_, mslot, moff, mt) =>
      valueExpr mt s!"Sol.structSlot ({slot}) {mslot}" moff) ++ "⟩"
  | _ => "0"

def leanTypeName (t : SolType) : Option String :=
  match t with
  | .value _ _ lean _ => some lean
  | .struct _ name _ _ => some name
  | _ => none

/-- `(params, result type, body, hashes)` of the accessor of a state variable. -/
def accessor (v : StateVar) : Option (List String × String × String × List String) := Id.run do
  let mut t := v.type
  let mut slot := toString v.slot
  let mut params : List String := []
  let mut hashes : List String := []
  while true do
    match t with
    | .mapping _ _ val =>
      let k := s!"k{params.length + 1}"
      params := params ++ [k]
      hashes := hashes ++ [s!"(64, [{k}, {slot}])"]
      slot := s!"Sol.mapSlot s.world ({slot}) {k}"
      t := val
    | _ => break
  let some ty := leanTypeName t | return none
  return some (params, ty, valueExpr t slot (if params.isEmpty then v.offset else 0), hashes)

partial def structsOf (t : SolType) : List SolType :=
  match t with
  | .mapping _ k v => structsOf k ++ structsOf v
  | .struct .. => [t]
  | _ => []

/-! ### `ONCHAIN` functions -/

/-- How an argument of Solidity type `abi` with encoding `enc` is passed: its Lean type, the
    constraint on its values (on `x`), and the calldata word (from `x`). -/
def argCoding (abi enc : String) : Except String (String × Option String × String) := do
  if enc == "asWord" then return ("Nat", some "_X_ < 2 ^ 256", "_X_")
  if enc != "asAbi" then throw s!"unknown encoding '{enc}' (asAbi, asWord)"
  if abi == "bool" then return ("Bool", none, "(if _X_ then 1 else 0)")
  if abi == "address" then return ("Nat", some "_X_ < 2 ^ 160", "_X_")
  if abi.startsWith "uint" then
    let n := (abi.drop 4).toNat?.getD 256
    return ("Nat", some s!"_X_ < 2 ^ {n}", "_X_")
  if abi.startsWith "int" then
    let n := (abi.drop 3).toNat?.getD 256
    return ("Int", some s!"-2 ^ {n - 1} ≤ _X_ ∧ _X_ < 2 ^ {n - 1}", "Int.toNat (_X_ % 2 ^ 256)")
  if abi.startsWith "bytes" && abi != "bytes" then
    let n := (abi.drop 5).toNat?.getD 32
    return ("Nat", some s!"_X_ < 2 ^ {8 * n}", s!"_X_ * 2 ^ {8 * (32 - n)}")
  throw s!"arguments of type {abi} are not supported (only value types: uintN, intN, address, bool, bytesN)"

/-- Normalise a Solidity type name of an annotation (`uint` is `uint256`). -/
def normType (t : String) : String :=
  if t == "uint" then "uint256" else if t == "int" then "int256" else
  if t == "byte" then "bytes1" else t

/-- An `ONCHAIN` function resolved against the ABI. -/
structure Resolved where
  ann : Onchain
  fn : Function
  /-- `(name, Lean type, constraint, word)` per argument. -/
  args : List (String × String × Option String × String)
  steps : Nat

def defaultSteps : Nat := 3000

def resolve (m : ContractModel) (o : Onchain) : Except Problem Resolved := do
  let cands := m.functions.filter (·.name == o.fn)
  if cands.isEmpty then
    let names := ", ".intercalate (m.functions.map (·.name))
    throw ⟨o.pos, s!"{m.name} has no external function '{o.fn}'",
      some (if names.isEmpty then "the contract has no external functions" else s!"its external functions: {names}")⟩
  let argTypes := o.types.dropLast
  let fit := cands.filter fun f => f.inputs.length == argTypes.length &&
    (f.inputs.zip argTypes).all fun (p, t) => normType t.sol == p.type
  let some f := fit.head? | do
    let sigs := "; ".intercalate (cands.map fun f => s!"{o.fn} : " ++ " -> ".intercalate
      ((f.inputs.map (·.type)) ++ [match f.outputs with | [] => "()" | [r] => r.type | _ => "tuple"]))
    throw ⟨o.pos, s!"the ONCHAIN signature does not match the Solidity function", some s!"expected {sigs}"⟩
  let ret := normType (o.types.getLast!.sol)
  let expRet := match f.outputs with | [] => "()" | [r] => r.type | _ => "tuple"
  if ret != expRet then
    throw ⟨o.pos, s!"{o.fn} returns {expRet}, not {ret}", some s!"end the signature with -> {expRet}"⟩
  let mut steps := defaultSteps
  for (k, v) in o.options do
    match k with
    | "steps" | "fuel" => steps := v.toNat!
    | "version" =>
      unless ["cancun", "Cancun"].contains v do
        throw ⟨o.pos, s!"EVM version {v} is not modelled", some "the machine models Cancun ([version: Cancun])"⟩
    | "exCPU" | "exMem" =>
      throw ⟨o.pos, s!"'{k}' is a Plutus execution budget", some "for the EVM, bound the execution with [steps: N]"⟩
    | _ => throw ⟨o.pos, s!"unknown ONCHAIN option '{k}'", some "options: [steps: N], [version: Cancun]"⟩
  let mut args : List (String × String × Option String × String) := []
  for ((p, t), i) in (f.inputs.zip argTypes).zipIdx do
    match argCoding p.type t.encoding with
    | .ok (ty, c, w) =>
      let n := leanName (if p.name.isEmpty then s!"arg{i}" else p.name)
      args := args ++ [(n, ty, c.map (·.replace "_X_" n), w.replace "_X_" n)]
    | .error e => throw ⟨o.pos, s!"argument {i + 1} of {o.fn}: {e}", none⟩
  return ⟨o, f, args, steps⟩

/-! ### The modules -/

def infoTerm (m : ContractModel) : String :=
  s!"\{ slots := {m.slots}, structSize := {m.structSize}, stringSlots := {m.stringSlots}, usesKeccak := {m.usesKeccak} }"

def onchainDefs (w : Writer) (r : Resolved) : Writer := Id.run do
  let n := leanName r.fn.name
  let ps := String.join (r.args.map fun (a, t, _, _) => s!"({a} : {t}) ")
  let as := String.join (r.args.map fun (a, _, _, _) => a ++ " ")
  let words := ", ".intercalate (r.args.map (·.2.2.2))
  let fuel := toString r.steps
  let mut w := w
  w := w.emit s!"/-- `{r.fn.signature}`, selector {hex r.fn.selector}: a call with these arguments. -/"
  w := w.emit s!"def {n}.env {ps}(env : Env) : Env :=\n  env.withCalldata (.ofAbi {hex r.fn.selector} [{words}])"
  let cs := r.args.filterMap (·.2.2.1)
  if !cs.isEmpty then
    w := w.emit s!"def {n}.inputs {ps}: Prop := {" ∧ ".intercalate cs}"
  w := w.emit s!"@[ual_onchain] def {n} {ps}(env : Env) (world : World) : Result :=\n  execute UALModel.code ({n}.env {as}env) world {fuel}"
  w := w.emit s!"def {n}.hashes {ps}(env : Env) (world : World) : List HashInput :=\n  hashesOf UALModel.code ({n}.env {as}env) world {fuel}"
  w := w.emit s!"def {n}.trace {ps}(env : Env) (world : World) : String :=\n  Replay.run UALModel.code ({n}.env {as}env) world {fuel}"
  return w.emit

def contractsModule (file : String) (models : List (ContractModel × String × List Resolved)) : String := Id.run do
  let mut w : Writer := {}
  w := w.emit "import UAL"
  w := w.emit ""
  w := w.emit s!"/-! Generated by blaster-evm from {commentSafe file}. Do not edit. -/"
  w := w.emit ""
  w := w.emit "open Evm UAL"
  w := w.emit ""
  for (m, bin, fns) in models do
    let ns := leanName m.name
    w := w.emit s!"namespace {ns}"
    w := w.emit ""
    w := w.emit s!"namespace UALModel"
    w := w.emit s!"#evm_contract_file code \"{bin}\""
    w := w.emit s!"def info : ContractInfo := {infoTerm m}"
    w := w.emit s!"end UALModel"
    w := w.emit ""
    -- struct types
    let mut seen : List String := []
    for v in m.vars do
      for t in structsOf v.type do
        if let .struct label name _ ms := t then
          if seen.contains name then continue
          seen := seen ++ [name]
          w := w.emit s!"/-- `{label}` (its value-type members). -/"
          w := w.emit s!"structure {leanName name} where"
          for (mn, _, _, mt) in ms do
            w := w.emit s!"  {leanName mn} : {(leanTypeName mt).getD "Nat"}"
          w := w.emit "deriving DecidableEq, Repr"
          w := w.emit ""
    for e in m.enums do
      let short := (e.name.splitOn ".").getLast!
      w := w.emit s!"/-! `enum {e.name}`: its members, as stored. -/"
      w := w.emit s!"namespace {leanName short}"
      for (mem, i) in e.members.zipIdx do
        w := w.emit s!"def {leanName mem} : Nat := {i}"
      w := w.emit s!"end {leanName short}"
      w := w.emit ""
    w := w.emit "/-! State variables, read from a snapshot of the storage. -/"
    for v in m.vars do
      let some (params, ty, body, hashes) := accessor v | continue
      let n := leanName v.name
      let ps := String.join (params.map fun k => s!" ({k} : Nat)")
      w := w.emit s!"/-- `{v.type.label} {v.name}` (slot {v.slot}{if v.offset != 0 then s!", byte {v.offset}" else ""}). -/"
      if params.isEmpty then
        w := w.emit s!"def {n} (s : Snapshot) : {ty} := {body}"
      else
        w := w.emit s!"@[ual_storage] def {n} (s : Snapshot){ps} : {ty} :=\n  {body}"
        w := w.emit s!"def {n}.hashes (s : Snapshot){ps} : List HashInput := [{", ".intercalate hashes}]"
    w := w.emit ""
    if !m.events.isEmpty then
      w := w.emit "/-! Events. -/"
      for e in m.events do
        if m.vars.any (·.name == e.name) || m.functions.any (·.name == e.name) then continue
        w := w.emit s!"/-- `event {e.signature}`. -/"
        w := w.emit s!"def {leanName e.name} : Event := ⟨{hex e.topic}⟩"
      w := w.emit ""
    let fuel := fns.foldl (fun a r => max a r.steps) defaultSteps
    w := w.emit "/-- A call to the contract with any calldata (`env.msg.calldata`). -/"
    w := w.emit s!"@[ual_onchain] def dispatch (env : Env) (world : World) : Result :=\n  execute UALModel.code env world {fuel}"
    w := w.emit s!"def dispatch.hashes (env : Env) (world : World) : List HashInput :=\n  hashesOf UALModel.code env world {fuel}"
    w := w.emit s!"def dispatch.trace (env : Env) (world : World) : String :=\n  Replay.run UALModel.code env world {fuel}"
    w := w.emit ""
    for r in fns do
      w := onchainDefs w r
    w := w.emit s!"end {ns}"
    w := w.emit ""
  return w.render

def predicatesNs (stem : String) : String := sanitize stem ++ "Predicates"

def predicatesModule (src file stem contractsMod : String) (contracts : List String)
    (preds : Array Predicate) : String × Array Segment := Id.run do
  let mut w : Writer := {}
  w := w.emit s!"import {contractsMod}"
  w := w.emit ""
  w := w.emit s!"/-! Generated by blaster-evm from {commentSafe file}: its PREDICATE annotations. Do not edit. -/"
  w := w.emit ""
  w := w.emit "open Evm UAL"
  w := w.emit ""
  w := w.emit s!"namespace {predicatesNs stem}"
  for p in preds do
    w := w.emit ""
    match p.contract with
    | some c =>
      w := w.emit s!"section\nopen {leanName c}"
      w := w.emitSpan src p.code
      w := w.emit "end"
    | none =>
      w := w.emit s!"section\nopen {" ".intercalate (contracts.map leanName)}"
      w := w.emitSpan src p.code
      w := w.emit "end"
  w := w.emit ""
  w := w.emit s!"end {predicatesNs stem}"
  return (w.render, w.map)

def propertyHeader (w : Writer) (predMod stem : String) (contracts : List String) : Writer :=
  w.emit s!"import {predMod}"
    |>.emit ""
    |>.emit s!"open Evm UAL {predicatesNs stem} {" ".intercalate (contracts.map leanName)}"
    |>.emit "set_option maxHeartbeats 0"
    |>.emit ""

/-- The file proving one property. -/
def propertyFile (src predMod stem : String) (contracts : List String) (p : Property) (timeout : Nat) :
    String × Array Segment := Id.run do
  let mut w := propertyHeader {} predMod stem contracts
  let c := leanName p.contract
  w := w.emit s!"namespace {c}.Properties"
  w := w.emit s!"open {c}"
  w := w.emit s!"#ual_property {leanName p.name} {c}.UALModel.info {timeout} :"
  w := w.emitSpan src p.body
  if let some t := p.tactic then
    w := w.emit "  := by"
    w := w.emitSpan src t
  w := w.emit s!"end {c}.Properties"
  return (w.render, w.map)

/-- The file checking that the statements elaborate (`blaster-evm check`). -/
def checkFile (src predMod stem : String) (contracts : List String) (ps : Array Property) :
    String × Array Segment := Id.run do
  let mut w := propertyHeader {} predMod stem contracts
  for p in ps do
    let c := leanName p.contract
    w := w.emit s!"namespace {c}.Properties"
    w := w.emit s!"open {c}"
    w := w.emit s!"#ual_check {leanName p.name} {c}.UALModel.info :"
    w := w.emitSpan src p.body
    w := w.emit s!"end {c}.Properties"
    w := w.emit ""
  return (w.render, w.map)

end UAL.Driver
