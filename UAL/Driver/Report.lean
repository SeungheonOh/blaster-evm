import Lean
import UAL.SExp
import UAL.Driver.Model
import UAL.Driver.Solidity

/-!
# Reporting

Terminal output: results, source excerpts, and counterexamples in Solidity terms. A
counterexample is the values of the statement's variables, and for every `ONCHAIN` call in
the statement, a replay of the call on the EVM model (`Evm.Replay.run`): the function and
arguments (decoded with the ABI), the storage it read (named after the state variables,
mapping entries included, using the keccak256 preimages of the replay), and the outcome
(the storage changes, the Ether sent, the events, or the revert reason).
-/

namespace UAL.Driver
open Lean

/-! ### Style -/

structure Style where
  color : Bool := false

def Style.c (s : Style) (code text : String) : String :=
  if s.color then s!"\x1b[{code}m{text}\x1b[0m" else text
def Style.bold (s : Style) := s.c "1"
def Style.dim (s : Style) := s.c "2"
def Style.red (s : Style) := s.c "31"
def Style.green (s : Style) := s.c "32"
def Style.yellow (s : Style) := s.c "33"
def Style.cyan (s : Style) := s.c "36"

/-! ### JSON access -/

def jNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
def jStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
def jArr (j : Json) (k : String) : Array Json := (j.getObjValAs? (Array Json) k).toOption.getD #[]
def jNats (j : Json) (k : String) : List Nat := (j.getObjValAs? (List Nat) k).toOption.getD []

/-! ### Values -/

def U256 : Nat := 2 ^ 256

def hexDigits (n : Nat) (width : Nat := 0) : String :=
  let d := String.mk (Nat.toDigits 16 n)
  String.mk (List.replicate (width - d.length) '0') ++ d

def fmtNat (n : Nat) : String := Id.run do
  if n == U256 - 1 then return "2^256 - 1 (max uint256)"
  if n + 10 ^ 6 ≥ U256 && n < U256 then return s!"2^256 - {U256 - n}"
  if n < 10 ^ 12 then return toString n
  for k in [1:257] do
    let p := 2 ^ k
    if n + 1000 ≥ p && n < p + 1000 then
      return if n == p then s!"2^{k}" else if n > p then s!"2^{k} + {n - p}" else s!"2^{k} - {p - n}"
  return "0x" ++ hexDigits n

abbrev Labels := List (Nat × String)

def fmtAddress (n : Nat) (labels : Labels := []) : String :=
  let a := n % 2 ^ 160
  match labels.lookup a with
  | some l => l
  | none =>
    let h := hexDigits a 40
    let stripped := (h.dropWhile (· == '0'))
    if stripped.length ≤ 6 then "0x…" ++ hexDigits a 4 else "0x" ++ h

def fmtSigned (bits v : Nat) : String :=
  let v := v % 2 ^ bits
  if v ≥ 2 ^ (bits - 1) then s!"-{2 ^ bits - v}" else toString v

/-- A word as a value of ABI type `abi`. -/
def fmtTyped (v : Nat) (abi : String) (labels : Labels := []) : String :=
  if abi == "address" || abi.startsWith "contract" then fmtAddress v labels
  else if abi == "bool" then (if v == 0 then "false" else "true")
  else if abi.startsWith "int" then fmtSigned ((abi.drop 3).toNat?.getD 256) v
  else if abi.startsWith "bytes" && abi != "bytes" then "0x" ++ hexDigits v
  else
    match labels.lookup v with
    | some l => if abi == "uint160" then l else fmtNat v
    | none => fmtNat v

/-- A storage value of type `t`. -/
def fmtStored (t : SolType) (v : Nat) (labels : Labels) (enums : List EnumDef := []) : String :=
  match t with
  | .value label bytes lean bits =>
    let v := v % 2 ^ (8 * bytes)
    let enum := if label.startsWith "enum " then enums.find? (·.name == label.drop 5) else none
    if let some e := enum then
      match e.members[v]? with
      | some n => s!"{(e.name.splitOn ".").getLast!}.{n}"
      | none => s!"{v} (not a member of {e.name})"
    else if lean == "Bool" then (if v == 0 then "false" else "true")
    else if lean == "Int" then fmtSigned bits v
    else if label.startsWith "address" || label.startsWith "contract " then fmtAddress v labels
    else fmtNat v
  | _ => fmtNat v

def bytesOfHex (s : String) : Array Nat := Id.run do
  let s := if s.startsWith "0x" then s.drop 2 else s
  let mut out : Array Nat := #[]
  for i in [0:s.length / 2] do
    out := out.push (hexToNat ((s.drop (2 * i)).take 2))
  return out

def wordAt (data : Array Nat) (off : Nat) : Nat :=
  (List.range 32).foldl (fun acc i => acc * 256 + data.getD (off + i) 0) 0

/-- Decode ABI values (value types, and `string`/`bytes`). -/
def decodeValues (data : Array Nat) (types : List String) (labels : Labels) : List String :=
  types.zipIdx.map fun (t, k) =>
    let w := wordAt data (32 * k)
    if t == "string" || t == "bytes" then
      let len := wordAt data w
      if len > 4096 || w + 32 + len > data.size then "…" else
      let raw := (data.extract (w + 32) (w + 32 + len)).toList
      if t == "string" then
        "\"" ++ (String.fromUTF8? (ByteArray.mk (raw.map (·.toUInt8)).toArray)).getD "…" ++ "\""
      else "0x" ++ String.join (raw.map (hexDigits · 2))
    else if t.endsWith "]" || t.startsWith "(" then "…"
    else fmtTyped w t labels

def panicReason (code : Nat) : String :=
  match code with
  | 0x01 => "assertion failed"
  | 0x11 => "arithmetic overflow or underflow"
  | 0x12 => "division or modulo by zero"
  | 0x21 => "invalid enum value"
  | 0x22 => "invalid storage byte array"
  | 0x31 => "pop on an empty array"
  | 0x32 => "array index out of bounds"
  | 0x41 => "out of memory"
  | 0x51 => "call to an uninitialised function"
  | c => s!"panic code {hex c}"
where hex (n : Nat) := "0x" ++ hexDigits n

def decodeRevert (m : ContractModel) (output : String) (labels : Labels) : String := Id.run do
  let data := bytesOfHex output
  if data.isEmpty then return "reverts (no reason)"
  if data.size < 4 then return s!"reverts with {output}"
  let sel := (List.range 4).foldl (fun acc i => acc * 256 + data[i]!) 0
  let some e := m.errors.find? (·.selector == sel)
    | return s!"reverts with an unknown error (selector 0x{hexDigits sel 8})"
  let rest := data.extract 4 data.size
  let vals := decodeValues rest (e.inputs.map (·.type)) labels
  if e.name == "Panic" then return s!"panics: {panicReason (wordAt rest 0)}"
  if e.name == "Error" then return s!"reverts: {vals.headD "…"}"
  let args := ", ".intercalate ((e.inputs.zip vals).map fun (p, v) =>
    if p.name.isEmpty then v else s!"{p.name}: {v}")
  return s!"reverts with {e.name}({args})"

/-! ### Naming storage slots -/

/-- keccak256 preimages: hash ↦ (length, words). -/
abbrev Preimages := List (Nat × Nat × List Nat)

/-- Names of the storage location `slot`: `(name, type)` per state variable stored there
    (several for packed slots), or mapping entries `m[k]` (with the struct member). -/
partial def slotNames (m : ContractModel) (pre : Preimages) (labels : Labels) (slot : Nat) :
    List (String × SolType × Nat) := Id.run do
  let direct := m.vars.filter fun v => v.slot == slot && match v.type with
    | .value .. => true | _ => false
  if !direct.isEmpty then return direct.map fun v => (v.name, v.type, v.offset)
  -- a struct state variable
  for v in m.vars do
    if let .struct _ _ _ ms := v.type then
      for (mn, ms, mo, mt) in ms do
        if v.slot + ms == slot then return [(s!"{v.name}.{mn}", mt, mo)]
  match mappingPath slot 0 with
  | some (name, t, off) =>
    match t with
    | .struct _ _ _ ms =>
      return (ms.filter (·.2.1 == off)).map fun (mn, _, mo, mt) => (s!"{name}.{mn}", mt, mo)
    | _ => if off == 0 then return [(name, t, 0)] else return []
  | none => return []
where
  keyText (t : SolType) (k : Nat) : String :=
    match t with
    | .value label .. =>
      if label.startsWith "address" || label.startsWith "contract " then fmtAddress k labels
      else fmtStored t k labels
    | _ => fmtNat k
  /-- `(name, value type, offset within the struct)` of a slot inside a mapping. -/
  mappingPath (slot depth : Nat) : Option (String × SolType × Nat) := do
    if depth > 6 then none
    let gap := max 1 m.structSize
    (List.range gap).findSome? fun off =>
      let h := (slot + U256 - off) % U256
      match pre.lookup h with
      | some (64, [key, parent]) =>
        match m.vars.find? (fun v => v.slot == parent && match v.type with | .mapping .. => true | _ => false) with
        | some v =>
          match v.type with
          | .mapping _ kt vt => some (s!"{v.name}[{keyText kt key}]", vt, off)
          | _ => none
        | none =>
          match mappingPath parent (depth + 1) with
          | some (name, .mapping _ kt vt, 0) => some (s!"{name}[{keyText kt key}]", vt, off)
          | _ => none
      | _ => none

def extractField (t : SolType) (off v : Nat) : Nat :=
  match t with
  | .value _ bytes .. => (v / 2 ^ (8 * off)) % 2 ^ (8 * bytes)
  | _ => v

/-- `(name, before, after?)` for a storage slot. -/
def describeSlot (m : ContractModel) (pre : Preimages) (labels : Labels) (slot before : Nat)
    (after : Option Nat) : List (String × String × Option String) :=
  match slotNames m pre labels slot with
  | [] => [(s!"storage[{fmtNat slot}]", fmtNat before, after.map fmtNat)]
  | names => names.map fun (n, t, off) =>
    (n, fmtStored t (extractField t off before) labels m.enums,
      after.map fun a => fmtStored t (extractField t off a) labels m.enums)

/-! ### Explaining a call -/

/-- The preimages known from a replay and from the counterexample's world. The replay's
    come first: they are the hashes the execution computed, while the world may also
    answer other inputs with the same values (only the hashes a statement involves are
    assumed collision-free). -/
def preimagesOf (traces : List Json) (world : Array Json) : Preimages := Id.run do
  let mut out : Preimages := []
  for t in traces do
    for k in jArr t "keccak" do
      out := out ++ [(jNat k "value", jNat k "len", jNats k "words")]
  for p in world do
    if let .ok (.app c [len, .list ws]) := SExp.parse (jStr p "raw") then
      if SExp.short c == "keccak" then
        if let (some l, some v) := (SExp.asNat? len, (jStr p "value").toNat?) then
          out := out ++ [(v, l, ws.filterMap SExp.asNat?)]
  return out

def labelsOf (env : Json) : Labels :=
  [(jNat env "caller" % 2 ^ 160, "msg.sender"), (jNat env "address" % 2 ^ 160, "this"),
   (jNat env "origin" % 2 ^ 160, "tx.origin")].foldl
    (fun acc (a, l) => if acc.any (·.1 == a) then acc else acc ++ [(a, l)]) []

/-- The function a call's calldata selects. -/
def callName (m : ContractModel) (t : Json) (labels : Labels) : String :=
  let size := jNat t "dataSize"
  let sel := jNat t "selector"
  if size == 0 then "receive() / fallback (no calldata)"
  else if size < 4 then s!"fallback ({size} bytes of calldata)"
  else match m.functions.find? (·.selector == sel) with
    | some f =>
      let args := jNats t "args"
      let vals := f.inputs.zipIdx.map fun (p, i) =>
        let v := args.getD i 0
        let s := if p.type.endsWith "]" || p.type == "string" || p.type == "bytes" || p.type.startsWith "("
          then "…" else fmtTyped v p.type (labels.filter (·.2 != p.name))
        if p.name.isEmpty then s else s!"{p.name}: {s}"
      s!"{f.name}({", ".intercalate vals})"
    | none => s!"unknown function (selector 0x{hexDigits sel 8})"

def decodeLog (m : ContractModel) (log : Json) (labels : Labels) : String :=
  let topics := jNats log "topics"
  match m.events.find? (fun e => topics.head? == some e.topic) with
  | none => s!"an anonymous log ({topics.length} topics)"
  | some e =>
    let data := bytesOfHex (jStr log "data")
    let nonIdx := (e.inputs.filter (!·.2)).map (·.1.type)
    let vals := decodeValues data nonIdx labels
    let rec go : List (AbiParam × Bool) → List Nat → List String → List String
      | [], _, _ => []
      | (p, true) :: ps, t :: ts, vs =>
        s!"{p.name}: {fmtTyped t p.type (labels.filter (·.2 != p.name))}" :: go ps ts vs
      | (p, true) :: ps, [], vs => s!"{p.name}: ?" :: go ps [] vs
      | (p, false) :: ps, ts, v :: vs => s!"{p.name}: {v}" :: go ps ts vs
      | (p, false) :: ps, ts, [] => s!"{p.name}: ?" :: go ps ts []
    s!"{e.name}({", ".intercalate (go e.inputs (topics.drop 1) vals)})"

/-- Rows `(label, text)` describing a replayed call. -/
def explainCall (s : Style) (m : ContractModel) (t : Json) (pre : Preimages) (labels : Labels) :
    List (String × String) := Id.run do
  let mut rows : List (String × String) := []
  let mut from_ := s!"{fmtAddress (jNat t "caller")}"
  if jNat t "value" != 0 then from_ := from_ ++ s!" · msg.value {fmtNat (jNat t "value")} wei"
  rows := rows ++ [("from", from_)]
  if jNat t "origin" % 2 ^ 160 != jNat t "caller" % 2 ^ 160 then
    rows := rows ++ [("tx.origin", fmtAddress (jNat t "origin"))]
  rows := rows ++ [("context", s!"this {fmtAddress (jNat t "address")} · balance {fmtNat (jNat t "balanceBefore")} wei · block {jNat t "number"}, timestamp {jNat t "timestamp"}")]
  -- the storage it read, before the call
  let mut seen : List Nat := []
  let mut state : List String := []
  for r in jArr t "sloads" do
    let k := jNat r "key"
    if seen.contains k then continue
    seen := seen ++ [k]
    let before := if (r.getObjVal? "before").isOk then jNat r "before" else jNat r "value"
    for (n, b, _) in describeSlot m pre labels k before none do
      state := state ++ [s!"{n} = {b}"]
  if !state.isEmpty then rows := rows ++ [("storage", ", ".intercalate state)]
  match jStr t "result" with
  | "success" =>
    rows := rows ++ [("outcome", s.green "succeeds")]
    let mut changes : List String := []
    for e in jArr t "storage" do
      let (b, a) := (jNat e "before", jNat e "after")
      if b == a then continue
      for (n, bs, as) in describeSlot m pre labels (jNat e "key") b (some a) do
        if some bs != as then changes := changes ++ [s!"{n}: {bs} → {s.bold (as.getD "")}"]
    for c in changes do rows := rows ++ [("", c)]
    for c in jArr t "calls" do
      let ok := (c.getObjValAs? Bool "success").toOption.getD true
      let v := jNat c "value"
      let what := if v == 0 then s!"calls {fmtAddress (jNat c "to") labels}"
        else s!"sends {fmtNat v} wei to {fmtAddress (jNat c "to") labels}"
      rows := rows ++ [("", what ++ (if ok then "" else s.dim " (the call fails)"))]
    for l in jArr t "logs" do
      rows := rows ++ [("", s!"emits {decodeLog m l labels}")]
    let out := bytesOfHex (jStr t "output")
    match m.functions.find? (·.selector == jNat t "selector") with
    | some f =>
      if !f.outputs.isEmpty && !out.isEmpty then
        rows := rows ++ [("", s!"returns ({", ".intercalate (decodeValues out (f.outputs.map (·.type)) labels)})")]
    | none => pure ()
    if changes.isEmpty && (jArr t "calls").isEmpty && (jArr t "logs").isEmpty then
      rows := rows ++ [("", s.dim "no state change")]
  | "revert" => rows := rows ++ [("outcome", s.yellow (decodeRevert m (jStr t "output") labels))]
  | "exception" =>
    rows := rows ++ [("outcome", s.yellow s!"halts exceptionally at pc {jNat t "pc"} ({jStr t "instr"})")]
  | "unsupported" =>
    rows := rows ++ [("outcome", s.yellow s!"reaches {jStr t "unsupported"} at pc {jNat t "pc"}, which the EVM model does not cover")]
  | "outOfFuel" =>
    rows := rows ++ [("outcome", s.yellow s!"does not finish within {jNat t "fuel"} steps"),
      ("hint", s!"raise the bound in the ONCHAIN annotation: [steps: {2 * jNat t "fuel"}]")]
  | r => rows := rows ++ [("outcome", r)]
  return rows

/-! ### Printing -/

def wrapText (s : String) (width : Nat) : List String := Id.run do
  if s.length ≤ width then return [s]
  let mut out : List String := []
  let mut cur := ""
  for w in s.splitOn " " do
    if cur.length + w.length + 1 > width && !cur.isEmpty then
      out := out ++ [cur]; cur := w
    else cur := if cur.isEmpty then w else cur ++ " " ++ w
  return out ++ [cur]

def rowsText (s : Style) (indent : String) (rows : List (String × String)) : List String :=
  let width := rows.foldl (fun a (k, _) => max a k.length) 0 + 2
  rows.flatMap fun (k, v) =>
    (wrapText v 96).zipIdx.map fun (part, i) =>
      let key := if i == 0 then k else ""
      indent ++ s.dim (key ++ String.mk (List.replicate (width - key.length) ' ')) ++ part

/-- Source lines `[from, to]` of `src`, numbered. -/
def excerpt (s : Style) (lines : Array String) (from_ to : Nat) (mark : Option (Nat × Nat) := none) :
    List String :=
  let w := (toString to).length
  ((List.range (to + 1 - from_)).map (· + from_)).flatMap fun l =>
    if l == 0 || l > lines.size then [] else
    let n := toString l
    let text := s.dim (String.mk (List.replicate (w - n.length + 4) ' ') ++ n ++ " │ ") ++ lines[l - 1]!.trimRight
    let marker := match mark with
      | some (ml, mc) =>
        if ml == l then [s.dim (String.mk (List.replicate (w + 5) ' ') ++ "│ ") ++
          String.mk (List.replicate (mc - 1) ' ') ++ s.red "^"] else []
      | none => []
    text :: marker

/-- A counterexample, for the terminal. -/
def counterexampleText (s : Style) (models : List ContractModel) (res : Json) : List String := Id.run do
  let vars := jArr res "vars"
  let calls := jArr res "calls"
  let world := jArr res "world"
  let traces := (calls.map fun c => (c.getObjVal? "trace").toOption.getD Json.null).toList
  let env := (vars.findSome? fun v => (v.getObjVal? "env").toOption) |>.getD
    (traces.headD (Json.mkObj []))
  -- addresses are named after the caller, the contract, and the address arguments of calls
  let mut labels := labelsOf env
  for c in calls do
    let cname := ((jStr c "fn").splitOn ".").head!
    let some m := models.find? (·.name == cname) | continue
    let some t := (c.getObjVal? "trace").toOption | continue
    let some f := m.functions.find? (·.selector == jNat t "selector") | continue
    let args := jNats t "args"
    for (p, i) in f.inputs.zipIdx do
      let a := args.getD i 0 % 2 ^ 160
      if p.type == "address" && !p.name.isEmpty && !labels.any (·.1 == a) then
        labels := labels ++ [(a, p.name)]
  let pre := preimagesOf traces world
  let mut out : List String := [s!"      {s.bold "Counterexample"}"]
  let mut rows : List (String × String) := []
  for v in vars do
    let ty := jStr v "type"
    let name := jStr v "name"
    if ty == "Env" || ty == "Evm.Env" then
      let e := (v.getObjVal? "env").toOption.getD (Json.mkObj [])
      let mut t := s!"msg.sender {fmtAddress (jNat e "caller")}"
      if jNat e "value" != 0 then t := t ++ s!" · msg.value {fmtNat (jNat e "value")} wei"
      t := t ++ s!" · this {fmtAddress (jNat e "address")} · balance {fmtNat (jNat e "balance")} wei"
      rows := rows ++ [(name, t)]
    else if ty == "Evm.Query → Nat" || ty == "Query → Nat" then continue
    else
      let value := jStr v "value"
      let shown := match value.toNat? with
        | some n => match labels.lookup n with
          | some l => fmtAddress n ++ (if l == name then "" else s!" ({l})")
          | none => fmtNat n
        | none => value
      rows := rows ++ [(name, shown)]
  out := out ++ rowsText s "        " rows
  let failing := (jArr res "conclusion").filter fun c => (c.getObjValAs? Bool "holds").toOption == some false
  if !failing.isEmpty then
    out := out ++ [s!"      {s.bold "Fails"}"]
    for c in failing do
      let text := jStr c "text"
      let ls := text.splitOn "\n"
      out := out ++ [s!"        {s.red "✗"} {ls.head!}"] ++ (ls.drop 1).map ("          " ++ ·)
  for c in calls do
    let fn := jStr c "fn"
    let cname := (fn.splitOn ".").head!
    let some m := models.find? (·.name == cname) | continue
    let some t := (c.getObjVal? "trace").toOption | continue
    out := out ++ [s!"      {s.bold s!"{cname}.{callName m t labels}"}"]
    out := out ++ rowsText s "        " (explainCall s m t pre labels)
  -- storage the statement reads beyond what the calls read
  let read := traces.flatMap fun t => (jArr t "sloads").toList.map (jNat · "key")
  let mut extra : List String := []
  for p in world do
    if let .ok (.app c [k]) := SExp.parse (jStr p "raw") then
      if SExp.short c == "storage" then
        if let (some k, some v) := (SExp.asNat? k, (jStr p "value").toNat?) then
          if read.contains k then continue
          if let some m := models.head? then
            for (n, b, _) in describeSlot m pre labels k v none do
              extra := extra ++ [s!"{n} = {b}"]
  if !extra.isEmpty then
    out := out ++ rowsText s "      " [("other storage", ", ".intercalate extra)]
  return out

end UAL.Driver
