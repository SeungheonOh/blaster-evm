import Lean
import UAL.Driver.Process
import UAL.Driver.Solc
import UAL.Driver.Solidity
import UAL.Driver.Model
import UAL.Driver.Gen
import UAL.Driver.Report

/-!
# `blaster-evm`: proving UAL annotations of Solidity contracts

```
blaster-evm [prove] FILE.sol|DIR …   prove every PROPERTY (the default command)
blaster-evm check FILE.sol|DIR …     only check that the annotations are well-formed and typed
blaster-evm list FILE.sol|DIR …      list the annotations
blaster-evm lean FILE.sol            generate the Lean files and print where they are
blaster-evm clean                    remove generated files and cached results
```

For each file: find the annotations and parse them with Lean's parser and the UAL grammar;
compile the file with solc; generate Lean (`UAL.Driver.Gen`); check that every statement
elaborates; then prove the properties one at a time, each in its own Lean process with
Blaster, under memory and CPU limits; replay and decode counterexamples; print a report.
Results are cached by the content of the generated Lean.
-/

namespace UAL.Driver
open Lean

/-! ### Options -/

structure Config where
  cmd : String := "prove"
  paths : Array String := #[]
  only : List String := []
  timeout : Nat := 120
  cache : Bool := true
  json : Bool := false
  verbose : Bool := false
  mem : String := "8G"
  cpu : String := "400%"

def usage : String := "usage: blaster-evm [prove|check|list|lean|clean] [options] FILE.sol|DIR …

Proves the UAL annotations (PROPERTY) of Solidity contracts with Blaster.

commands:
  prove      prove every property (default)
  check      only check that the annotations parse and their statements elaborate
  list       list the annotations of each contract
  lean       generate the Lean files and print where they are
  clean      remove generated files and cached results

options:
  --only NAME       only properties whose name (or Contract.name) contains NAME (repeatable)
  --timeout S       solver timeout per property, in seconds (default 120)
  --no-cache        do not reuse earlier results
  --json            print the results as JSON
  --mem SIZE        memory limit of each check (default 8G)
  --cpu PERCENT     CPU quota of each check (default 400%)
  -v, --verbose     show the Lean commands run and their output
  -h, --help        show this help

environment: SOLC (a solc binary), NO_COLOR, CHECK_MEM, CHECK_CPU"

def parseArgs (args : List String) (c : Config := {}) : Except String Config :=
  match args with
  | [] => .ok c
  | "--only" :: n :: rest => parseArgs rest { c with only := c.only ++ [n] }
  | "--timeout" :: n :: rest => match n.toNat? with
    | some t => parseArgs rest { c with timeout := t }
    | none => .error s!"--timeout expects a number of seconds, not '{n}'"
  | "--no-cache" :: rest => parseArgs rest { c with cache := false }
  | "--json" :: rest => parseArgs rest { c with json := true }
  | "--mem" :: m :: rest => parseArgs rest { c with mem := m }
  | "--cpu" :: m :: rest => parseArgs rest { c with cpu := m }
  | "-h" :: rest | "--help" :: rest => parseArgs rest { c with cmd := "help" }
  | "-v" :: rest | "--verbose" :: rest => parseArgs rest { c with verbose := true }
  | a :: rest =>
    if a.startsWith "-" then .error s!"unknown option '{a}'"
    else if c.paths.isEmpty && c.cmd == "prove" && ["prove", "check", "list", "lean", "clean"].contains a then
      parseArgs rest { c with cmd := a }
    else parseArgs rest { c with paths := c.paths.push a }

/-! ### The installation -/

structure Install where
  root : System.FilePath
  sysroot : System.FilePath
  work : System.FilePath
  leanPath : List System.FilePath

def Install.lean (i : Install) : String := (i.sysroot / "bin" / "lean").toString
def Install.genRoot (i : Install) : System.FilePath := i.work / "gen"
def Install.dynlib (i : Install) : System.FilePath :=
  i.root / "vendor" / "Lean-blaster" / ".lake" / "build" / "lib" / "libBlaster.so"
def Install.env (i : Install) : Array (String × String) :=
  #[("LEAN_PATH", ":".intercalate ((i.genRoot :: i.leanPath).map (·.toString)))]

def findInstall : IO Install := do
  let root ← match ← IO.getEnv "BLASTER_EVM_ROOT" with
    | some r => pure (System.FilePath.mk r)
    | none =>
      let app ← IO.appPath
      pure ((app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)).getD ".")
  let sysroot ← match ← IO.getEnv "LEAN_SYSROOT" with
    | some s => pure (System.FilePath.mk s)
    | none => Lean.findSysroot
  let leanPath := [root / ".lake" / "build" / "lib" / "lean",
    root / "vendor" / "Lean-blaster" / ".lake" / "build" / "lib" / "lean",
    sysroot / "lib" / "lean"]
  return { root, sysroot, work := root / ".lake" / "ual", leanPath }

/-! ### Output -/

structure Out where
  style : Style
  tty : Bool
  json : Bool
  verbose : Bool
  /-- A transient status line is shown. -/
  status : IO.Ref Bool

def Out.clear (o : Out) : IO Unit := do
  if ← o.status.get then
    IO.print "\r\x1b[K"
    (← IO.getStdout).flush
    o.status.set false

def Out.line (o : Out) (s : String := "") : IO Unit := do
  if o.json then return
  o.clear
  IO.println s
  (← IO.getStdout).flush

def Out.err (o : Out) (s : String) : IO Unit := do
  o.clear
  IO.eprintln s

def Out.progress (o : Out) (s : String) : IO Unit := do
  if !o.tty || o.json then return
  o.clear
  IO.print (o.style.dim s!"    … {s}")
  (← IO.getStdout).flush
  o.status.set true

/-- Run `act`, showing `what` with the elapsed time while it runs (on a terminal). -/
def Out.timed (o : Out) (what : String) (act : IO α) : IO α := do
  if !o.tty || o.json then return ← act
  let done ← IO.mkRef false
  let start ← IO.monoMsNow
  o.progress what
  let ticker ← IO.asTask (prio := .dedicated) do
    repeat
      IO.sleep 250
      if ← done.get then break
      let s := ((← IO.monoMsNow) - start) / 1000
      if s > 0 then o.progress s!"{what} ({s}s)"
  try act finally
    done.set true
    discard <| IO.wait ticker
    o.clear

def secs (ms : Nat) : String :=
  let t := (ms + 50) / 100
  s!"{t / 10}.{t % 10}s"

/-- A problem in the Solidity file, rustc style. -/
def showProblem (o : Out) (file : String) (lines : Array String) (p : Problem) : IO Unit := do
  let s := o.style
  o.line s!"{s.bold s!"{file}:{p.pos.line}:{p.pos.col}:"} {s.red "error:"} {(p.msg.splitOn "\n").head!}"
  for l in (p.msg.splitOn "\n").drop 1 do o.line s!"    {l}"
  for l in excerpt s lines p.pos.line p.pos.line (some (p.pos.line, p.pos.col)) do o.line l
  if let some h := p.hint then o.line s!"  {s.cyan "hint:"} {h}"

/-! ### Lean messages -/

structure Msg where
  severity : String
  line : Nat
  col : Nat
  text : String

def readMessages (out : String) : Array Msg := Id.run do
  let mut ms : Array Msg := #[]
  for l in out.splitOn "\n" do
    if !l.startsWith "{" then continue
    let .ok j := Json.parse l | continue
    let pos := (j.getObjVal? "pos").toOption.getD (Json.mkObj [])
    ms := ms.push ⟨jStr j "severity", jNat pos "line", jNat pos "column" + 1, jStr j "data"⟩
  return ms

def resultOf (m : Msg) : Option Json :=
  if m.severity == "information" && m.text.startsWith "UAL-RESULT " then
    (Json.parse (m.text.drop 11)).toOption
  else none

/-- Run Lean on a generated file. -/
def runLean (inst : Install) (cfg : Config) (o : Out) (file : System.FilePath) (runtime : Nat)
    (extra : Array String := #[]) : IO IO.Process.Output := do
  let lim : Limits := { mem := cfg.mem, cpu := cfg.cpu, systemd := ← detectSystemd }
  let args := #["--json", s!"--load-dynlib={inst.dynlib}", "-R", inst.genRoot.toString] ++ extra ++ #[file.toString]
  if o.verbose then o.err s!"$ LEAN_PATH=… {inst.lean} {" ".intercalate args.toList}"
  let r ← runLimited lim inst.lean args inst.env inst.root runtime
  if o.verbose then o.err (r.stdout ++ r.stderr)
  return r

/-! ### Per file -/

structure Item where
  file : String
  contract : String
  name : String
  line : Nat
  status : String
  time : Nat := 0
  cached : Bool := false
  result : Json := Json.null
  errors : Array (Nat × Nat × String) := #[]

def Item.json (i : Item) : Json :=
  Json.mkObj [("file", i.file), ("contract", i.contract), ("property", i.name), ("line", i.line),
    ("status", i.status), ("time", i.time), ("cached", i.cached), ("result", i.result),
    ("errors", Json.arr (i.errors.map fun (l, c, t) => Json.mkObj [("line", l), ("column", c), ("message", t)]))]

def selected (cfg : Config) (c n : String) : Bool :=
  cfg.only.isEmpty || cfg.only.any fun p => ((c ++ "." ++ n).splitOn p).length > 1

def contentHash (s : String) : String := hexDigits (hash s).toNat 16

/-- Write `text` to `path` unless it already holds it. -/
def writeIfChanged (path : System.FilePath) (text : String) : IO Unit := do
  if let some d := path.parent then IO.FS.createDirAll d
  if ← path.pathExists then
    if (← IO.FS.readFile path) == text then return
  IO.FS.writeFile path text

/-- A stamp of the toolchain (the compiled UAL and EVM modules), part of every cache key. -/
def toolStamp (inst : Install) : IO String := do
  let mut s := ""
  for m in ["UAL/Command.olean", "UAL/Evm.olean", "EvmBlaster.olean", "EvmBlaster/Machine.olean"] do
    let p := inst.root / ".lake" / "build" / "lib" / "lean" / m
    if ← p.pathExists then
      let md ← p.metadata
      s := s ++ s!"{m}:{md.modified.sec}:{md.byteSize};"
  return s

structure Prepared where
  src : String
  lines : Array String
  ann : Annotations
  models : List ContractModel
  stem : String
  modDir : System.FilePath
  modName : String
  contracts : List String

/-- Messages of a generated file at Solidity lines (by the source map) or else as internal. -/
def mapErrors (map : Array Segment) (ms : Array Msg) : Array (Nat × Nat × String) :=
  ms.filter (·.severity == "error") |>.map fun m =>
    match locate map m.line with
    | some l => (l, m.col, m.text)
    | none => (0, 0, m.text)

def showErrors (o : Out) (file : String) (lines : Array String) (errs : Array (Nat × Nat × String)) : IO Unit := do
  let s := o.style
  for (l, c, t) in errs do
    let first := (t.splitOn "\n").head!
    if l == 0 then
      o.line s!"      {s.red "error:"} {first}"
    else
      o.line s!"      {s.bold s!"{file}:{l}:{c}:"} {s.red "error:"} {first}"
    for x in ((t.splitOn "\n").drop 1).take 12 do o.line s!"        {x}"
    if l != 0 then
      for x in excerpt s lines l l (some (l, c)) do o.line ("  " ++ x)

/-- Parse, compile and generate; compile the generated modules. -/
def prepare (inst : Install) (cfg : Config) (o : Out) (pEnv : Environment) (file : String) :
    IO (Option Prepared) := do
  let s := o.style
  let src ← IO.FS.readFile file
  let lines := (src.splitOn "\n").toArray
  let ann ← match parseAnnotations pEnv file src with
    | .ok a => pure a
    | .error p => showProblem o file lines p; return none
  if ann.properties.isEmpty && ann.onchain.isEmpty && ann.predicates.isEmpty then
    o.line (s.dim s!"  no UAL annotations in {file}")
    return some { src, lines, ann, models := [], stem := "", modDir := ".", modName := "", contracts := [] }
  let (solc, ver) ← findSolc src (fun m => o.progress m)
  o.line s!"{s.bold s!"blaster-evm · {file}"}{s.dim s!"  (solc {vstr ver})"}"
  let out ← o.timed "compiling with solc" (compile solc file [] "cancun")
  let (contractsJ, enums) ← match out with
    | .ok j => pure ((j.getObjVal? "contracts").toOption.getD (Json.mkObj []),
        enumsOf ((j.getObjVal? "ast").toOption.getD Json.null))
    | .error e => o.line s!"  {s.red "error:"} solc rejects the file\n{e}"; return none
  -- the annotated contracts
  let annotated := ann.contracts.filter fun c =>
    ann.onchain.any (·.contract == c.name) || ann.properties.any (·.contract == c.name)
  let mut models : List ContractModel := []
  for c in annotated do
    let some j := (contractsJ.getObjVal? c.name).toOption
      | o.line s!"  {s.red "error:"} solc produced no contract {c.name}"; return none
    let m := { buildModel c.name j with
      enums := enums.filter fun e => e.name.startsWith (c.name ++ ".") || !e.name.contains '.' }
    if m.bytecode.isEmpty then
      showProblem o file lines ⟨⟨c.line, 1⟩, s!"{c.kind} {c.name} has no runtime bytecode (abstract or an interface)",
        some "annotate a deployable contract"⟩
      return none
    models := models ++ [m]
  let mut resolved : List (ContractModel × List Resolved) := []
  for m in models do
    let mut fns : List Resolved := []
    for a in ann.onchain.filter (·.contract == m.name) do
      match resolve m a with
      | .ok r => fns := fns ++ [r]
      | .error p => showProblem o file lines p; return none
    if m.functions.any (·.name == "dispatch") || m.vars.any (·.name == "dispatch") then
      o.line s!"  {s.yellow "warning:"} {m.name} has a member named 'dispatch'; the call to any function is {m.name}.dispatch"
    resolved := resolved ++ [(m, fns)]
  let stem := sanitize ((System.FilePath.mk file).fileStem.getD "Contract")
  let contracts := models.map (·.name)
  -- generate
  let binDir := inst.work / "bin"
  IO.FS.createDirAll binDir
  let mut withBins : List (ContractModel × String × List Resolved) := []
  for (m, fns) in resolved do
    let bin := binDir / s!"{contentHash m.bytecode}.bin"
    writeIfChanged bin m.bytecode
    withBins := withBins ++ [(m, bin.toString, fns)]
  let contractsText := contractsModule file withBins
  let (predsText0, _) := predicatesModule src file stem "_" contracts ann.predicates
  let h := contentHash (contractsText ++ predsText0 ++ (← toolStamp inst))
  let modName := s!"UALGen.{stem}_{h}"
  let modDir := inst.genRoot / "UALGen" / s!"{stem}_{h}"
  let (predsText, predMap) := predicatesModule src file stem s!"{modName}.Contracts" contracts ann.predicates
  for (name, text) in [("Contracts", contractsText), ("Predicates", predsText)] do
    let lf := modDir / s!"{name}.lean"
    writeIfChanged lf text
    let olean := modDir / s!"{name}.olean"
    if ← olean.pathExists then continue
    let r ← o.timed s!"compiling the {if name == "Contracts" then "contract model" else "predicates"}"
      (runLean inst cfg o lf 1800 #["-o", olean.toString])
    let ms := readMessages r.stdout
    if r.exitCode != 0 || ms.any (·.severity == "error") then
      if name == "Predicates" then
        o.line s!"  {s.red "error:"} in a PREDICATE annotation"
        showErrors o file lines (mapErrors predMap ms)
      else
        o.line s!"  {s.red "internal error:"} the generated contract model ({lf}) does not compile"
        showErrors o file lines (mapErrors #[] ms)
        if ms.isEmpty then o.line (r.stderr.trim)
      if ← olean.pathExists then IO.FS.removeFile olean
      return none
  return some { src, lines, ann, models, stem, modDir, modName, contracts }

def propLine (o : Out) (i : Item) (width : Nat := 36) : IO Unit := do
  let s := o.style
  let (sym, what) := match i.status with
    | "proved" => (s.green "✓", "proved")
    | "checked" => (s.green "✓", "well-typed")
    | "falsified" => (s.red "✗", s.red "counterexample")
    | "unknown" => (s.yellow "?", s.yellow "unknown")
    | "error" => (s.red "!", s.red "error")
    | st => (s.yellow "?", st)
  let pad := String.mk (List.replicate (width - min width i.name.length) ' ')
  let t := if i.status == "checked" then "" else s.dim (secs i.time ++ if i.cached then " (cached)" else "")
  o.line s!"    {sym} {i.name}{pad} {what}  {t}"

def statementExcerpt (o : Out) (p : Prepared) (prop : Property) : IO Unit := do
  let first := prop.pos.line
  let last := (posOf p.src prop.body.stop).line
  for l in excerpt o.style p.lines first (min last (first + 11)) do o.line ("  " ++ l)
  if last > first + 11 then o.line (o.style.dim "             …")

/-- Check the statements of the selected properties; return the errors per property. -/
def checkAll (inst : Install) (cfg : Config) (o : Out) (p : Prepared) (props : Array Property) :
    IO (Option (Array (Option (Array (Nat × Nat × String))))) := do
  if props.isEmpty then return some #[]
  let (text, map) := checkFile p.src s!"{p.modName}.Predicates" p.stem p.contracts props
  let f := p.modDir / "Check.lean"
  writeIfChanged f text
  let r ← o.timed "checking the statements" (runLean inst cfg o f 900)
  let ms := readMessages r.stdout
  if ms.isEmpty && r.exitCode != 0 then
    o.line s!"  {o.style.red "error:"} Lean failed: {r.stderr.trim}"
    return none
  -- attribute each message to the property whose statement precedes it
  let owner (line : Nat) : Nat := Id.run do
    let mut k := 0
    for (seg, i) in map.zipIdx do
      if seg.gen ≤ line + 1 then k := i
    return k
  let mut out : Array (Option (Array (Nat × Nat × String))) := props.map fun _ => none
  for m in ms do
    if m.severity != "error" then continue
    let i := owner m.line
    let e := match locate map m.line with
      | some l => (l, m.col, m.text)
      | none => ((props[i]!).pos.line, (props[i]!).pos.col, m.text)
    out := out.modify i fun x => some ((x.getD #[]).push e)
  return some out

def proveOne (inst : Install) (cfg : Config) (o : Out) (p : Prepared) (prop : Property) : IO Item := do
  let base : Item := { file := "", contract := prop.contract, name := prop.name, line := prop.pos.line, status := "" }
  let (text, map) := propertyFile p.src s!"{p.modName}.Predicates" p.stem p.contracts prop cfg.timeout
  let key := contentHash (text ++ p.modName ++ toString cfg.timeout)
  let f := p.modDir / "Properties" / s!"{sanitize prop.contract}_{sanitize prop.name}.lean"
  writeIfChanged f text
  let cacheFile := inst.work / "cache" / s!"{key}.json"
  if cfg.cache then
    if ← cacheFile.pathExists then
      if let .ok j := Json.parse (← IO.FS.readFile cacheFile) then
        return { base with status := jStr j "status", time := jNat j "time", cached := true, result := j }
  let start ← IO.monoMsNow
  let r ← o.timed s!"proving {prop.contract}.{prop.name}" (runLean inst cfg o f (2 * cfg.timeout + 300))
  let elapsed := (← IO.monoMsNow) - start
  let ms := readMessages r.stdout
  let errs := mapErrors map ms
  if let some j := ms.findSome? resultOf then
    let st := jStr j "status"
    if st != "unknown" then
      writeIfChanged cacheFile j.compress
    return { base with status := st, time := jNat j "time", result := j, errors := errs }
  if !errs.isEmpty then
    return { base with status := "error", time := elapsed, errors := errs }
  let detail := if r.stderr.trim.isEmpty then "" else ": " ++ r.stderr.trim
  let why := if r.exitCode == 137 || r.exitCode == 9 || (r.stderr.splitOn "memory").length > 1
    then s!"the check was stopped: it reached the memory limit ({cfg.mem}); raise it with --mem"
    else s!"Lean stopped without a result (exit code {r.exitCode}){detail}"
  let result := Json.mkObj [("status", "unknown"), ("why", Json.str why)]
  return { base with status := "unknown", time := elapsed, result }

def showItem (o : Out) (p : Prepared) (prop : Property) (i : Item) (width : Nat) : IO Unit := do
  propLine o i width
  let s := o.style
  match i.status with
  | "falsified" =>
    o.line (s.dim s!"      {i.file}:{prop.pos.line}")
    statementExcerpt o p prop
    for l in counterexampleText s p.models i.result do o.line l
    o.line
  | "unknown" =>
    o.line (s.dim s!"      {jStr i.result "why"}")
  | "error" => showErrors o i.file p.lines i.errors
  | _ => pure ()

def runFile (inst : Install) (cfg : Config) (o : Out) (pEnv : Environment) (file : String) :
    IO (Option (Array Item)) := do
  let s := o.style
  let some p ← prepare inst cfg o pEnv file | return none
  let mut items : Array Item := #[]
  for c in p.models do
    let props := p.ann.properties.filter fun x => x.contract == c.name && selected cfg x.contract x.name
    let nOn := (p.ann.onchain.filter (·.contract == c.name)).size
    o.line s!"  {s.bold c.name}{s.dim s!"  {c.bytecode.length / 2} bytes · {nOn} ONCHAIN · {props.size} propert{if props.size == 1 then "y" else "ies"}"}"
    for w in c.warnings do o.line s!"    {s.yellow "warning:"} {w}"
    let width := props.foldl (fun a x => max a (x.name.length + 2)) 30
    let some checks ← checkAll inst cfg o p props | return none
    for (prop, errs) in props.zip checks do
      let base : Item := { file, contract := c.name, name := prop.name, line := prop.pos.line, status := "checked" }
      if let some es := errs then
        let i := { base with status := "error", errors := es }
        showItem o p prop i width
        items := items.push i
        continue
      if cfg.cmd == "check" then
        propLine o base width
        items := items.push base
        continue
      let i ← proveOne inst cfg o p prop
      let i := { i with file }
      showItem o p prop i width
      items := items.push i
  return some items

/-! ### Commands -/

partial def solFiles (path : System.FilePath) : IO (Array String) := do
  if ← path.isDir then
    let mut out : Array String := #[]
    for e in (← path.readDir).qsort (·.fileName < ·.fileName) do
      if e.fileName.startsWith "." || e.fileName == "node_modules" || e.fileName == "lib" then continue
      out := out ++ (← solFiles e.path)
    return out
  else if path.extension == some "sol" then
    let text ← IO.FS.readFile path
    if (text.splitOn "/*@").length > 1 then return #[path.toString]
  return #[]

def summary (o : Out) (items : Array Item) (elapsed : Nat) (failedFiles : Nat) : IO Unit := do
  let s := o.style
  let count (st : String) := (items.filter (·.status == st)).size
  let mut parts : List String := []
  if count "proved" > 0 then parts := parts ++ [s.green s!"{count "proved"} proved"]
  if count "checked" > 0 then parts := parts ++ [s.green s!"{count "checked"} well-typed"]
  if count "falsified" > 0 then parts := parts ++ [s.red s!"{count "falsified"} falsified"]
  if count "unknown" > 0 then parts := parts ++ [s.yellow s!"{count "unknown"} unknown"]
  if count "error" > 0 then parts := parts ++ [s.red s!"{count "error"} with errors"]
  if failedFiles > 0 then parts := parts ++ [s.red s!"{failedFiles} file{if failedFiles == 1 then "" else "s"} not checked"]
  o.line
  o.line s!"{s.bold "Summary:"} {if parts.isEmpty then "nothing to check" else ", ".intercalate parts}{s.dim s!"  ({secs elapsed})"}"

def listFile (o : Out) (pEnv : Environment) (file : String) : IO Bool := do
  let s := o.style
  let src ← IO.FS.readFile file
  let lines := (src.splitOn "\n").toArray
  match parseAnnotations pEnv file src with
  | .error p => showProblem o file lines p; return false
  | .ok a =>
    o.line (s.bold file)
    if !a.predicates.isEmpty then
      o.line s!"  {s.dim "PREDICATE"} {a.predicates.size} block{if a.predicates.size == 1 then "" else "s"} (line{if a.predicates.size == 1 then "" else "s"} {", ".intercalate (a.predicates.toList.map (toString ·.pos.line))})"
    for c in a.contracts do
      let on := a.onchain.filter (·.contract == c.name)
      let ps := a.properties.filter (·.contract == c.name)
      if on.isEmpty && ps.isEmpty then continue
      o.line s!"  {s.bold c.name}"
      for x in on do
        let opts := String.join (x.options.map fun (k, v) => s!"[{k}: {v}] ")
        let sig := " -> ".intercalate (x.types.map fun t => if t.encoding == "asAbi" then t.sol else s!"\{ {t.sol} : {t.encoding} }")
        o.line s!"    {s.cyan "ONCHAIN"}  {opts}{x.fn} : {sig}  {s.dim s!"line {x.pos.line}"}"
      for x in ps do
        o.line s!"    {s.cyan "PROPERTY"} {x.name}  {s.dim s!"line {x.pos.line}"}"
    return true

unsafe def loadParserEnv (inst : Install) : IO Environment := do
  Lean.initSearchPath inst.sysroot inst.leanPath
  Lean.enableInitializersExecution
  importModules #[{ module := `UAL.Syntax }] {} (loadExts := true)

unsafe def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args with
    | .ok c => pure c
    | .error e => IO.eprintln s!"blaster-evm: {e}\n\n{usage}"; return 2
  if cfg.cmd == "help" then
    IO.println usage; return 0
  let envMem := (← IO.getEnv "CHECK_MEM").getD "8G"
  let envCpu := (← IO.getEnv "CHECK_CPU").getD "400%"
  let cfg := { cfg with
    mem := if cfg.mem == "8G" then envMem else cfg.mem
    cpu := if cfg.cpu == "400%" then envCpu else cfg.cpu }
  let tty ← (← IO.getStdout).isTty
  let noColor := (← IO.getEnv "NO_COLOR").isSome || (← IO.getEnv "TERM") == some "dumb"
  let o : Out := { style := { color := tty && !noColor }, tty, json := cfg.json, verbose := cfg.verbose,
                   status := ← IO.mkRef false }
  let inst ← findInstall
  if cfg.cmd == "clean" then
    if ← inst.work.pathExists then IO.FS.removeDirAll inst.work
    o.line s!"removed {inst.work}"
    return 0
  if cfg.paths.isEmpty then
    IO.eprintln usage; return 2
  let mut files : Array String := #[]
  for p0 in cfg.paths do
    let p := if p0.length > 1 && p0.endsWith "/" then p0.dropRightWhile (· == '/') else p0
    unless ← System.FilePath.pathExists p do
      IO.eprintln s!"blaster-evm: no such file or directory: {p}"; return 2
    let fs ← solFiles p
    if fs.isEmpty && !(← System.FilePath.isDir p) then files := files.push p else files := files ++ fs
  if files.isEmpty then
    IO.eprintln "blaster-evm: no Solidity files with UAL annotations (/*@ … @*/) found"; return 2
  let pEnv ← loadParserEnv inst
  if cfg.cmd == "list" then
    let mut ok := true
    for f in files do ok := (← listFile o pEnv f) && ok
    return if ok then 0 else 1
  if cfg.cmd == "lean" then
    for f in files do
      let some p ← prepare inst cfg o pEnv f | return 1
      let props := p.ann.properties.filter fun x => selected cfg x.contract x.name
      let mut paths := #[p.modDir / "Contracts.lean", p.modDir / "Predicates.lean"]
      for prop in props do
        let (text, _) := propertyFile p.src s!"{p.modName}.Predicates" p.stem p.contracts prop cfg.timeout
        let path := p.modDir / "Properties" / s!"{sanitize prop.contract}_{sanitize prop.name}.lean"
        writeIfChanged path text
        paths := paths.push path
      for x in paths do IO.println x.toString
      IO.println s!"(run one with: LEAN_PATH={inst.genRoot}:… lean --load-dynlib={inst.dynlib} FILE)"
    return 0
  let start ← IO.monoMsNow
  let (items, failed) ← withCheckLock (fun m => o.progress m) do
    let mut items : Array Item := #[]
    let mut failed := 0
    for f in files do
      match ← runFile inst cfg o pEnv f with
      | some is => items := items ++ is
      | none => failed := failed + 1
      o.line
    return (items, failed)
  if cfg.json then
    IO.println (Json.arr (items.map (·.json))).pretty
  else
    summary o items ((← IO.monoMsNow) - start) failed
  let ok := failed == 0 && items.all fun i => i.status == "proved" || i.status == "checked"
  return if ok then 0 else 1

end UAL.Driver

unsafe def main (args : List String) : IO UInt32 := UAL.Driver.main args
