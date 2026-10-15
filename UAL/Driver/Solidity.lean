import Lean
import UAL.Syntax

/-!
# Finding and parsing UAL annotations in Solidity

An annotation is a block comment `/*@ … @*/`. The scanner finds them (skipping strings and
ordinary comments) together with the contracts of the file; each annotation is then parsed
with Lean's parser and the UAL grammar (`UAL.Syntax`). The text given to the parser is the
annotation padded with the whitespace of everything before it, so that every position the
parser reports, and every position recorded in the syntax tree, is a position in the
Solidity file.
-/

namespace UAL.Driver
open Lean

structure Pos where
  line : Nat
  col : Nat  -- 1-based
deriving Inhabited, BEq

/-- The 1-based line and column of byte offset `off`. -/
def posOf (src : String) (off : String.Pos) : Pos :=
  let before := (src.extract 0 off)
  let lines := before.splitOn "\n"
  ⟨lines.length, (lines.getLast!.length) + 1⟩

structure Contract where
  name : String
  kind : String
  line : Nat
  bodyStart : String.Pos
  bodyEnd : String.Pos
deriving Inhabited

structure RawAnnotation where
  /-- Offset of the text after `/*@`. -/
  start : String.Pos
  stop : String.Pos
deriving Inhabited

structure Problem where
  pos : Pos
  msg : String
  hint : Option String := none

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- Contracts and annotations of a Solidity source. -/
partial def scan (src : String) : Except Problem (Array Contract × Array RawAnnotation) := do
  let mut cs : Array Contract := #[]
  let mut anns : Array RawAnnotation := #[]
  let mut depth := 0
  let mut pending : Option (String × String × Nat) := none
  let mut open_ : Array (Nat × Nat) := #[]  -- (index in cs, depth)
  let mut i : String.Pos := 0
  let stop := src.endPos
  while i < stop do
    let c := src.get i
    let rest := src.extract i stop
    if rest.startsWith "/*@" then
      let body := i + "/*@"
      match (src.extract body stop).splitOn "@*/" with
      | before :: _ :: _ =>
        let e := body + before
        anns := anns.push ⟨body, e⟩
        i := e + "@*/"
      | _ => throw ⟨posOf src i, "unterminated annotation: missing '@*/'", none⟩
    else if rest.startsWith "//" then
      match rest.posOf '\n' with
      | p => i := i + (rest.extract 0 p)
    else if rest.startsWith "/*" then
      match (rest.drop 2).splitOn "*/" with
      | before :: _ :: _ => i := i + "/*" + before + "*/"
      | _ => i := stop
    else if c == '"' || c == '\'' then
      let mut j := src.next i
      while j < stop && src.get j != c do
        j := if src.get j == '\\' then src.next (src.next j) else src.next j
      i := src.next j
    else if c == '{' then
      depth := depth + 1
      if let some (kind, name, line) := pending then
        cs := cs.push ⟨name, kind, line, i, stop⟩
        open_ := open_.push (cs.size - 1, depth)
        pending := none
      i := src.next i
    else if c == '}' then
      if let some (idx, d) := open_.back? then
        if d == depth then
          cs := cs.modify idx ({ · with bodyEnd := i })
          open_ := open_.pop
      depth := depth - 1
      i := src.next i
    else if c.isAlpha || c == '_' then
      let mut j := i
      while j < stop && isIdentChar (src.get j) do j := src.next j
      let word := src.extract i j
      let prevOk := i == 0 || !isIdentChar (src.get (src.prev i))
      if prevOk && (word == "contract" || word == "library" || word == "interface") then
        -- the declared name follows
        let mut k := j
        while k < stop && (src.get k).isWhitespace do k := src.next k
        let mut l := k
        while l < stop && isIdentChar (src.get l) do l := src.next l
        if l > k then pending := some (word, src.extract k l, (posOf src i).line)
        i := l
      else i := j
    else i := src.next i
  return (cs, anns)

/-! ### Parsed annotations -/

/-- A source range of the Solidity file. -/
structure Span where
  start : String.Pos
  stop : String.Pos
deriving Inhabited

structure OnchainType where
  /-- The Solidity type (`uint256`, `address`, …), `()` for unit. -/
  sol : String
  encoding : String := "asAbi"
deriving Inhabited

structure Onchain where
  contract : String
  fn : String
  options : List (String × String)
  types : List OnchainType
  pos : Pos
deriving Inhabited

structure Property where
  contract : String
  name : String
  body : Span
  tactic : Option Span
  pos : Pos
deriving Inhabited

structure Predicate where
  /-- `none`: file-level (all contracts). -/
  contract : Option String
  code : Span
  pos : Pos
deriving Inhabited

structure Annotations where
  contracts : Array Contract
  predicates : Array Predicate := #[]
  onchain : Array Onchain := #[]
  properties : Array Property := #[]
deriving Inhabited

/-- The text of `src` before `off`, with every character but newlines replaced by as many
    spaces as its UTF-8 bytes: prefixing a substring with it keeps its byte offsets and its
    line numbers (and its columns, as the line of an annotation usually starts with
    whitespace). -/
def padding (src : String) (off : String.Pos) : String :=
  String.mk ((src.extract 0 off).toList.flatMap fun c =>
    if c == '\n' then ['\n'] else List.replicate c.utf8Size ' ')

def spanOf (stx : Syntax) : Option Span := do
  return ⟨← stx.getPos?, ← stx.getTailPos?⟩

/-- Parse an error message `<file>:line:col: msg` of the parser. -/
def parseErrorPos (msg : String) : Pos × String :=
  match msg.splitOn ":" with
  | l :: c :: rest => (⟨l.trim.toNat!, c.trim.toNat! + 1⟩, ":".intercalate rest |>.trim)
  | _ => (⟨1, 1⟩, msg)

def optionsOf (stx : Syntax) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  for o in stx.getArgs do
    -- `[k: v, …]`
    for f in o[1].getSepArgs do
      let key := f[0].getId.toString
      let v := f[2][0]
      let value := if v.isOfKind numLitKind then toString v.isNatLit?.get! else v.getId.toString
      out := out ++ [(key, value)]
  return out

def typeOf (stx : Syntax) : OnchainType :=
  match stx.getNumArgs with
  | 1 => ⟨stx[0].getId.toString, "asAbi"⟩
  | 2 => ⟨"()", "asAbi"⟩
  | _ => ⟨stx[1].getId.toString, stx[3].getId.toString⟩

/-- Parse the annotations of a Solidity source. -/
def parseAnnotations (env : Environment) (file src : String) : Except Problem Annotations := do
  let (cs, raws) ← scan src
  let mut a : Annotations := { contracts := cs }
  let owner (off : String.Pos) : Option String × Bool :=
    let inner := cs.filter fun c => c.bodyStart < off && off < c.bodyEnd
    match inner.back? with
    | some c => (some c.name, true)
    | none => ((cs.find? fun c => c.bodyStart > off).map (·.name), false)
  for r in raws do
    let text := padding src r.start ++ src.extract r.start r.stop
    let pos := posOf src r.start
    let stx ← match Parser.runParserCategory env `ual_annotation text file with
      | .ok stx => pure stx
      | .error e =>
        let (p, m) := parseErrorPos (e.drop (file.length + 1))
        throw ⟨p, m, some "annotations are PREDICATE, ONCHAIN, PROPERTY (see docs/annotations.md)"⟩
    let (contract, inside) := owner r.start
    -- report at the annotation's keyword
    let pos := posOf src (stx.getPos?.getD r.start)
    let kind := stx.getKind
    if kind == ``UAL.uplcDataAnnotation then
      throw ⟨pos, "UPLC_DATA has no counterpart for Solidity: data layouts come from the compiler", none⟩
    if kind == ``UAL.predicateAnnotation then
      let cmds := stx[1].getArgs
      if let (some s, some e) := (cmds[0]?.bind (·.getPos?), cmds.back?.bind (·.getTailPos?)) then
        a := { a with predicates := a.predicates.push ⟨if inside then contract else none, ⟨s, e⟩, pos⟩ }
      continue
    let some c := contract
      | throw ⟨pos, "annotation not attached to any contract", some "place it inside a contract"⟩
    if kind == ``UAL.onchainAnnotation then
      let types := stx[4].getSepArgs.toList.map typeOf
      let o : Onchain := ⟨c, stx[2].getId.toString, optionsOf stx[1], types, posOf src (stx[2].getPos?.getD r.start)⟩
      a := { a with onchain := a.onchain.push o }
    else if kind == ``UAL.propertyAnnotation then
      let some body := spanOf stx[3] | throw ⟨pos, "empty PROPERTY statement", none⟩
      let tac := if stx[4].getNumArgs > 0 then spanOf stx[4][2] else none
      let name := stx[1].getId.toString
      if a.properties.any (fun p => p.contract == c && p.name == name) then
        throw ⟨posOf src (stx[1].getPos?.getD r.start), s!"duplicate property name '{name}' in {c}", none⟩
      let p : Property := ⟨c, name, body, tac, posOf src (stx[1].getPos?.getD r.start)⟩
      a := { a with properties := a.properties.push p }
  return a

end UAL.Driver
