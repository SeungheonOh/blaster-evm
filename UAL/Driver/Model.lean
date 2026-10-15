import Lean
import EvmBlaster.Keccak

/-!
# The contract model

From the compiler's standard JSON output: the state variables (storage layout: slots,
packed offsets, mappings, structs), the functions, events and errors (ABI), and the
runtime bytecode.
-/

namespace UAL.Driver
open Lean

/-- A storage type, as far as the front end gives accessors for it. -/
inductive SolType where
  /-- A value type: its label, size in bytes and Lean type (`Nat`, `Bool`, `Int`). -/
  | value (label : String) (bytes : Nat) (lean : String) (bits : Nat)
  | mapping (label : String) (key : SolType) (value : SolType)
  /-- A struct: its name and its value-type members `(name, slot, offset, type)`. -/
  | struct (label : String) (name : String) (bytes : Nat) (members : List (String × Nat × Nat × SolType))
  | string (label : String)
  | unsupported (label : String)
deriving Inhabited

def SolType.label : SolType → String
  | .value l .. | .mapping l .. | .struct l .. | .string l | .unsupported l => l

structure StateVar where
  name : String
  slot : Nat
  offset : Nat
  type : SolType
deriving Inhabited

structure AbiParam where
  name : String
  type : String
deriving Inhabited

structure Function where
  name : String
  signature : String
  selector : Nat
  inputs : List AbiParam
  outputs : List AbiParam
  mutability : String
deriving Inhabited

structure EventDef where
  name : String
  signature : String
  topic : Nat
  inputs : List (AbiParam × Bool)
deriving Inhabited

structure ErrorDef where
  name : String
  signature : String
  selector : Nat
  inputs : List AbiParam
deriving Inhabited

/-- An enum: its canonical name (`C.E`) and its members. -/
structure EnumDef where
  name : String
  members : List String
deriving Inhabited

structure ContractModel where
  name : String
  bytecode : String
  vars : List StateVar
  functions : List Function
  events : List EventDef
  errors : List ErrorDef
  slots : Nat
  structSize : Nat
  stringSlots : List Nat
  usesKeccak : Bool
  warnings : List String
  enums : List EnumDef := []
deriving Inhabited

/-- The enums declared in a syntax tree. -/
partial def enumsOf (ast : Json) : List EnumDef :=
  match ast with
  | .obj _ =>
    let here := if (ast.getObjValAs? String "nodeType").toOption == some "EnumDefinition" then
      [⟨(ast.getObjValAs? String "canonicalName").toOption.getD ((ast.getObjValAs? String "name").toOption.getD ""),
        ((ast.getObjValAs? (Array Json) "members").toOption.getD #[]).toList.map fun m =>
          (m.getObjValAs? String "name").toOption.getD ""⟩]
      else []
    let kids := match ast with
      | .obj kvs => kvs.foldl (fun acc _ v => acc ++ enumsOf v) []
      | _ => []
    here ++ kids
  | .arr xs => xs.toList.flatMap enumsOf
  | _ => []

def leanTypeOf (label : String) : Option (String × Nat) :=
  let l := label.replace "address payable" "address"
  if l == "bool" then some ("Bool", 8)
  else if l.startsWith "int" then some ("Int", (l.drop 3).toNat?.getD 256)
  else if l.startsWith "uint" || l == "address" || (l.startsWith "bytes" && l != "bytes")
      || l.startsWith "contract " || l.startsWith "enum " then some ("Nat", 256)
  else none

partial def storageTypeOf (types : Json) (tid : String) : SolType := Id.run do
  let some t := (types.getObjVal? tid).toOption | return .unsupported tid
  let label := (t.getObjValAs? String "label").toOption.getD tid
  let enc := (t.getObjValAs? String "encoding").toOption.getD ""
  let bytes := ((t.getObjValAs? String "numberOfBytes").toOption.bind String.toNat?).getD 32
  if enc == "mapping" then
    let key := storageTypeOf types ((t.getObjValAs? String "key").toOption.getD "")
    let value := storageTypeOf types ((t.getObjValAs? String "value").toOption.getD "")
    match key with
    | .value .. => return .mapping label key value
    | _ => return .unsupported label
  if enc == "bytes" then return .string label
  if enc == "inplace" && label.startsWith "struct " then
    let name := ((label.drop 7).splitOn ".").getLast!.map fun c => if c.isAlphanum then c else '_'
    let mut members : List (String × Nat × Nat × SolType) := []
    for m in (t.getObjValAs? (Array Json) "members").toOption.getD #[] do
      let mt := storageTypeOf types ((m.getObjValAs? String "type").toOption.getD "")
      if let .value .. := mt then
        members := members ++ [((m.getObjValAs? String "label").toOption.getD "",
          ((m.getObjValAs? String "slot").toOption.bind String.toNat?).getD 0,
          (m.getObjValAs? Nat "offset").toOption.getD 0, mt)]
    return .struct label name bytes members
  if enc == "inplace" then
    if let some (lean, bits) := leanTypeOf label then
      return .value label bytes lean (if lean == "Int" then bits else 8 * bytes)
  return .unsupported label

partial def abiType (j : Json) : String :=
  let t := (j.getObjValAs? String "type").toOption.getD ""
  if t.startsWith "tuple" then
    let comps := (j.getObjValAs? (Array Json) "components").toOption.getD #[]
    "(" ++ ",".intercalate (comps.toList.map abiType) ++ ")" ++ t.drop 5
  else t

def params (j : Json) (key : String) : List AbiParam :=
  ((j.getObjValAs? (Array Json) key).toOption.getD #[]).toList.map fun p =>
    ⟨(p.getObjValAs? String "name").toOption.getD "", abiType p⟩

def keccakNat (s : String) : Nat := Evm.Keccak.keccak256 s.toUTF8.data

def hexToNat (s : String) : Nat :=
  s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10)) 0

/-- Whether the bytecode contains opcode `op` (outside PUSH data). -/
def hasOpcode (code : String) (op : Nat) : Bool := Id.run do
  let bytes := (List.range (code.length / 2)).map fun i => hexToNat ((code.drop (2 * i)).take 2)
  let arr := bytes.toArray
  let mut i := 0
  while i < arr.size do
    let o := arr[i]!
    if o == op then return true
    i := i + 1 + (if 0x60 ≤ o && o ≤ 0x7f then o - 0x5f else 0)
  return false

def buildModel (name : String) (j : Json) : ContractModel := Id.run do
  let mut warnings : List String := []
  let dep := (j.getObjVal? "evm" >>= (·.getObjVal? "deployedBytecode")).toOption.getD (Json.mkObj [])
  let code := (dep.getObjValAs? String "object").toOption.getD ""
  if (dep.getObjVal? "immutableReferences").toOption.any (· != Json.mkObj []) then
    warnings := warnings ++ ["uses immutable variables, whose values are not in the runtime bytecode: they read as 0"]
  let layout := (j.getObjVal? "storageLayout").toOption.getD (Json.mkObj [])
  let types := (layout.getObjVal? "types").toOption.getD (Json.mkObj [])
  let mut vars : List StateVar := []
  let mut slots := 0
  let mut structSize := 0
  let mut strings : List Nat := []
  for v in (layout.getObjValAs? (Array Json) "storage").toOption.getD #[] do
    let st := storageTypeOf types ((v.getObjValAs? String "type").toOption.getD "")
    let slot := ((v.getObjValAs? String "slot").toOption.bind String.toNat?).getD 0
    let off := (v.getObjValAs? Nat "offset").toOption.getD 0
    let vname := (v.getObjValAs? String "label").toOption.getD ""
    let size := match st with
      | .struct _ _ b _ => max 1 ((b + 31) / 32)
      | _ => 1
    slots := max slots (slot + size)
    match st with
    | .unsupported l => warnings := warnings ++ [s!"state variable '{vname}' ({l}) has no accessor"]
    | .string _ => strings := strings ++ [slot]
    | .mapping .. =>
      let rec structIn : SolType → Nat
        | .mapping _ _ v => match v with
          | .struct _ _ b _ => max (max 1 ((b + 31) / 32)) (structIn v)
          | _ => structIn v
        | _ => 0
      structSize := max structSize (structIn st)
      vars := vars ++ [⟨vname, slot, off, st⟩]
    | _ => vars := vars ++ [⟨vname, slot, off, st⟩]
  let abi := (j.getObjValAs? (Array Json) "abi").toOption.getD #[]
  let ids := (j.getObjVal? "evm" >>= (·.getObjVal? "methodIdentifiers")).toOption.getD (Json.mkObj [])
  let mut functions : List Function := []
  let mut events : List EventDef := []
  let mut errors : List ErrorDef := []
  for e in abi do
    let kind := (e.getObjValAs? String "type").toOption.getD ""
    let ename := (e.getObjValAs? String "name").toOption.getD ""
    let ins := params e "inputs"
    let sig := s!"{ename}({",".intercalate (ins.map (·.type))})"
    if kind == "function" then
      let sel := hexToNat ((ids.getObjValAs? String sig).toOption.getD "0")
      functions := functions ++ [⟨ename, sig, sel, ins, params e "outputs",
        (e.getObjValAs? String "stateMutability").toOption.getD ""⟩]
    else if kind == "event" then
      let idx := ((e.getObjValAs? (Array Json) "inputs").toOption.getD #[]).toList.map fun p =>
        (p.getObjValAs? Bool "indexed").toOption.getD false
      events := events ++ [⟨ename, sig, keccakNat sig, ins.zip idx⟩]
    else if kind == "error" then
      errors := errors ++ [⟨ename, sig, keccakNat sig / 2 ^ 224, ins⟩]
  errors := errors ++ [⟨"Error", "Error(string)", 0x08c379a0, [⟨"message", "string"⟩]⟩,
                       ⟨"Panic", "Panic(uint256)", 0x4e487b71, [⟨"code", "uint256"⟩]⟩]
  return { name, bytecode := code, vars, functions, events, errors, slots, structSize,
           stringSlots := strings, usesKeccak := hasOpcode code 0x20, warnings }

end UAL.Driver
