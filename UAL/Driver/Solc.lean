import Lean
import UAL.Driver.Process

/-!
# The Solidity compiler

The compiler is chosen to satisfy the file's `pragma solidity`: `$SOLC` if set, else a
`solc` on `PATH` whose version fits, else the newest fitting release, downloaded once from
binaries.soliditylang.org (checked against its published SHA-256) into
`~/.cache/blaster-evm/solc`. Compilation uses the standard JSON interface.
-/

namespace UAL.Driver
open Lean

abbrev Version := Nat × Nat × Nat

def parseVersion (s : String) : Option Version :=
  match ((s.splitOn "+").head!.splitOn "-").head!.splitOn "." with
  | [a, b, c] => do return (← a.toNat?, ← b.toNat?, ← c.toNat?)
  | _ => none

def vlt (a b : Version) : Bool := a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- The constraints `(op, version)` of the `pragma solidity` lines. -/
def pragmaConstraints (src : String) : List (String × Version) := Id.run do
  let mut out : List (String × Version) := []
  for part in (src.splitOn "pragma solidity").drop 1 do
    let spec := ((part.splitOn ";").head!.splitOn "||").head!
    for w in (spec.split Char.isWhitespace).filter (· ≠ "") do
      let op := ["^", "~", ">=", "<=", ">", "<", "="].find? (w.startsWith ·) |>.getD "="
      if let some v := parseVersion (w.drop op.length) then out := out ++ [(op, v)]
  return out

def satisfies (v : Version) (cons : List (String × Version)) : Bool :=
  cons.all fun (op, w) =>
    match op with
    | "=" => v == w
    | ">=" => !vlt v w
    | ">" => vlt w v
    | "<=" => !vlt w v
    | "<" => vlt v w
    | "^" => !vlt v w && vlt v (if w.1 == 0 then (0, w.2.1 + 1, 0) else (w.1 + 1, 0, 0))
    | "~" => !vlt v w && vlt v (w.1, w.2.1 + 1, 0)
    | _ => true

def solcVersion (path : String) : IO (Option Version) := do
  try
    let out ← runQuiet path #["--version"]
    for l in out.stdout.splitOn "\n" do
      if l.startsWith "Version: " then
        return parseVersion ((l.drop 9).splitOn "+").head!
    return none
  catch _ => return none

def cacheDir : IO System.FilePath := do
  let base ← match ← IO.getEnv "XDG_CACHE_HOME" with
    | some d => pure (System.FilePath.mk d)
    | none => pure (System.FilePath.mk ((← IO.getEnv "HOME").getD "/tmp") / ".cache")
  return base / "blaster-evm" / "solc"

def vstr (v : Version) : String := s!"{v.1}.{v.2.1}.{v.2.2}"

def download (cons : List (String × Version)) (log : String → IO Unit) : IO (String × Version) := do
  let plat := if System.Platform.isOSX then "macosx-amd64" else "linux-amd64"
  let dir ← cacheDir
  IO.FS.createDirAll dir
  let list := dir / "list.json"
  let url := s!"https://binaries.soliditylang.org/{plat}"
  let r ← runQuiet "curl" #["-sSfL", "-A", "blaster-evm", "-o", list.toString, s!"{url}/list.json"]
  if r.exitCode != 0 then
    throw (IO.userError s!"cannot fetch the solc release list ({r.stderr.trim}); set SOLC to a solc binary")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile list))
  let builds ← IO.ofExcept (j.getObjValAs? (Array Json) "builds")
  let mut best : Option (Version × String × String) := none
  for b in builds do
    let some v := (b.getObjValAs? String "version").toOption.bind parseVersion | continue
    if (b.getObjValAs? Bool "prerelease").toOption == some true || !satisfies v cons then continue
    if best.all (fun (w, _, _) => vlt w v) then
      best := some (v, (b.getObjValAs? String "path").toOption.getD "", (b.getObjValAs? String "sha256").toOption.getD "")
  let some (v, path, sha) := best | throw (IO.userError "no solc release satisfies the pragma")
  let dest := dir / s!"solc-{vstr v}"
  if ← dest.pathExists then return (dest.toString, v)
  log s!"downloading solc {vstr v}"
  let part := dir / s!"solc-{vstr v}.part"
  let r ← runQuiet "curl" #["-sSfL", "-A", "blaster-evm", "-o", part.toString, s!"{url}/{path}"]
  if r.exitCode != 0 then throw (IO.userError s!"downloading solc failed: {r.stderr.trim}")
  let h ← runQuiet "sha256sum" #[part.toString]
  if "0x" ++ (h.stdout.splitOn " ").head! != sha then
    IO.FS.removeFile part
    throw (IO.userError s!"checksum mismatch for solc {vstr v}")
  discard <| runQuiet "chmod" #["+x", part.toString]
  IO.FS.rename part dest
  return (dest.toString, v)

/-- A solc binary satisfying the source's pragma, and its version. -/
def findSolc (src : String) (log : String → IO Unit) : IO (String × Version) := do
  let cons := pragmaConstraints src
  if let some p ← IO.getEnv "SOLC" then
    let some v ← solcVersion p | throw (IO.userError s!"SOLC={p} is not a working solc binary")
    unless satisfies v cons do throw (IO.userError s!"SOLC={p} is solc {vstr v}, which does not satisfy the pragma")
    return (p, v)
  let mut cands : Array String := #["solc"]
  let dir ← cacheDir
  if ← dir.pathExists then
    for e in ← dir.readDir do
      if e.fileName.startsWith "solc-" && !e.fileName.endsWith ".part" then cands := cands.push e.path.toString
  for c in cands do
    if let some v ← solcVersion c then
      if satisfies v cons then return (c, v)
  download cons log

/-- Compile `file` with solc; return the standard JSON output for the file's contracts
    (`contracts`) and its syntax tree (`ast`). -/
def compile (solc : String) (file : System.FilePath) (remaps : List String) (evm : String) :
    IO (Except String Json) := do
  let file ← IO.FS.realPath file
  let some dir := file.parent | return .error "no directory"
  let some name := file.fileName | return .error "no file name"
  let input := Json.mkObj [
    ("language", "Solidity"),
    ("sources", Json.mkObj [(name, Json.mkObj [("urls", Json.arr #[file.toString])])]),
    ("settings", Json.mkObj [
      ("optimizer", Json.mkObj [("enabled", true), ("runs", (200 : Nat))]),
      ("evmVersion", Json.str evm),
      ("remappings", toJson remaps),
      ("outputSelection", Json.mkObj [("*", Json.mkObj [("", toJson ["ast"]), ("*", toJson [
        "abi", "storageLayout", "evm.methodIdentifiers", "evm.deployedBytecode.object",
        "evm.deployedBytecode.immutableReferences", "evm.deployedBytecode.linkReferences"])])])])]
  let allow := ",".intercalate (dir.toString :: remaps.map fun r => (r.splitOn "=").getLast!)
  let out ← runLimited {} solc #["--standard-json", "--allow-paths", allow] #[] dir 600 (some input.compress)
  match Json.parse out.stdout with
  | .error _ => return .error s!"solc failed: {out.stderr.trim}{out.stdout.trim}"
  | .ok j =>
    let errs := (j.getObjValAs? (Array Json) "errors").toOption.getD #[]
    let fatal := errs.filter fun e => (e.getObjValAs? String "severity").toOption == some "error"
    if !fatal.isEmpty then
      return .error ("\n".intercalate (fatal.toList.map fun e =>
        ((e.getObjValAs? String "formattedMessage").toOption.getD "").trimRight))
    let cs := (j.getObjVal? "contracts" >>= (·.getObjVal? name)).toOption.getD (Json.mkObj [])
    let ast := (j.getObjVal? "sources" >>= (·.getObjVal? name) >>= (·.getObjVal? "ast")).toOption.getD Json.null
    return .ok (Json.mkObj [("contracts", cs), ("ast", ast)])

end UAL.Driver
