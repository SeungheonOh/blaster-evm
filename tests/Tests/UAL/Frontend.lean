import UAL.Driver.Solidity
import UAL.Driver.Gen
import UAL.Driver.Report

/-!
# The UAL front end: scanning, parsing, signatures, generation, decoding

Unit tests of `blaster-evm`'s front end, without solc or Blaster: the annotations of a
Solidity source are found and parsed with the UAL grammar, `ONCHAIN` signatures are
checked against an ABI, Lean is generated, and values are decoded for counterexamples.
-/

namespace Tests.UAL
open Lean UAL.Driver

def sample : String := "// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/*@ PREDICATE
def small (n : Nat) : Prop := n < 100
@*/

/// not an annotation: \"/*@ PROPERTY fake : True @*/\"
// nor this: /*@ PROPERTY fake2 : True @*/
contract Box {
    uint256 public value;
    string constant s = \"}{\";

    /*@ ONCHAIN [steps: 2000] set : { uint256 : asAbi } -> () @*/
    function set(uint256 v) external { value = v; }

    /*@ PROPERTY set_sets :
      ∀ (v : Nat) (env : Env) (world : World),
        isSuccessful (set v env world) → Box.value (after world (set v env world)) = v
    @*/

    /*@ PROPERTY by_hand : True := by trivial @*/
}

contract Other { }
"

/-- Parse with the environment of this file (which has the UAL grammar). -/
def parse (src : String) : CoreM (Except Problem Annotations) := do
  return parseAnnotations (← getEnv) "t.sol" src

/-- info: contracts: [Box, Other]
predicates: 1 (line 4, file level: true)
onchain: Box.set [(steps, 2000)] [uint256 asAbi, () asAbi] line 14
property: Box.set_sets line 17, tactic: false
property: Box.by_hand line 22, tactic: true
-/
#guard_msgs in
#eval show CoreM Unit from do
  match ← parse sample with
  | .error p => IO.println s!"error {p.pos.line}:{p.pos.col} {p.msg}"
  | .ok a =>
    IO.println s!"contracts: {a.contracts.toList.map (·.name)}"
    for p in a.predicates do
      IO.println s!"predicates: {a.predicates.size} (line {p.pos.line}, file level: {p.contract.isNone})"
    for o in a.onchain do
      IO.println s!"onchain: {o.contract}.{o.fn} {o.options} {o.types.map fun t => s!"{t.sol} {t.encoding}"} line {o.pos.line}"
    for p in a.properties do
      IO.println s!"property: {p.contract}.{p.name} line {p.pos.line}, tactic: {p.tactic.isSome}"

-- The text of a property statement is the Solidity text.
/-- info: "∀ (v : Nat) (env : Env) (world : World),\n        isSuccessful (set v env world) → Box.value (after world (set v env world)) = v" -/
#guard_msgs in
#eval show CoreM Unit from do
  let .ok a ← parse sample | throwError "parse"
  let p := a.properties[0]!
  IO.println (repr (sample.extract p.body.start p.body.stop))

/-! ### Errors, at their Solidity position -/

def errorOf (src : String) : CoreM String := do
  match ← parse src with
  | .error p => return s!"{p.pos.line}:{p.pos.col}: {p.msg}{match p.hint with | some h => s!" (hint: {h})" | none => ""}"
  | .ok _ => return "no error"

/-- info: "3:21: expected ':' (hint: annotations are PREDICATE, ONCHAIN, PROPERTY (see docs/annotations.md))" -/
#guard_msgs in
#eval errorOf "contract C {\n  function f() external {}\n  /*@ PROPERTY oops True @*/\n}"

/-- info: "2:7: UPLC_DATA has no counterpart for Solidity: data layouts come from the compiler" -/
#guard_msgs in
#eval errorOf "contract C {\n  /*@ UPLC_DATA Datum @*/\n}"

/-- info: "1:1: unterminated annotation: missing '@*/'" -/
#guard_msgs in
#eval errorOf "/*@ PROPERTY p : True \ncontract C {}"

/-- info: "1:5: annotation not attached to any contract (hint: place it inside a contract)" -/
#guard_msgs in
#eval errorOf "/*@ PROPERTY p : True @*/"

/-- info: "3:16: duplicate property name 'p' in C" -/
#guard_msgs in
#eval errorOf "contract C {\n  /*@ PROPERTY p : True @*/\n  /*@ PROPERTY p : False @*/\n}"

/-! ### The annotation forms of the UAL specification

The `ONCHAIN` and `PROPERTY` forms of the UAL README, with its Plinth names, parse (the
types are only checked against an ABI later). -/

/-- info: "ok: 1 onchain, 1 property" -/
#guard_msgs in
#eval show CoreM Unit from do
  let src := "contract C {
  /*@ ONCHAIN [version: PlutusV3] [exCPU: 1000000, exMem: 200000]
      mintingContract : { CurrencySymbol : asData } -> { ScriptContext : asData } -> BuiltinUnit @*/
  /*@ PROPERTY successfulMint :
      ∀ (pparamsCs : Nat) (ctx : Nat), pparamsCs = ctx → ctx = pparamsCs @*/
}"
  match ← parse src with
  | .ok a => IO.println (repr s!"ok: {a.onchain.size} onchain, {a.properties.size} property")
  | .error p => IO.println (repr s!"{p.pos.line}:{p.pos.col}: {p.msg}")

/-! ### Signatures against the ABI -/

def boxModel : ContractModel :=
  { name := "Box", bytecode := "00", vars := [], events := [], errors := [], slots := 1,
    structSize := 0, stringSlots := [], usesKeccak := false, warnings := [],
    functions := [⟨"set", "set(uint256)", 0x60fe47b1, [⟨"v", "uint256"⟩], [], "nonpayable"⟩,
                  ⟨"pay", "pay(address,bool,bytes4,int8)", 0x12345678,
                    [⟨"to", "address"⟩, ⟨"flag", "bool"⟩, ⟨"tag", "bytes4"⟩, ⟨"d", "int8"⟩], [⟨"", "uint256"⟩], "payable"⟩] }

def resolveText (fn : String) (opts : List (String × String)) (types : List OnchainType) : String :=
  match resolve boxModel ⟨"Box", fn, opts, types, ⟨1, 1⟩⟩ with
  | .ok r => s!"ok steps {r.steps}: " ++ ", ".intercalate (r.args.map fun (n, t, c, w) => s!"{n} : {t} [{c.getD "-"}] {w}")
  | .error p => s!"{p.msg}{match p.hint with | some h => s!" (hint: {h})" | none => ""}"

/-- info: "ok steps 3000: v : Nat [v < 2 ^ 256] v" -/
#guard_msgs in #eval resolveText "set" [] [⟨"uint256", "asAbi"⟩, ⟨"()", "asAbi"⟩]

/-- info: "ok steps 3000: v : Nat [v < 2 ^ 256] v" -/
#guard_msgs in #eval resolveText "set" [] [⟨"uint", "asWord"⟩, ⟨"()", "asAbi"⟩]

/-- info: "ok steps 500: to : Nat [to < 2 ^ 160] to, flag : Bool [-] (if flag then 1 else 0), tag : Nat [tag < 2 ^ 32] tag * 2 ^ 224, d : Int [-2 ^ 7 ≤ d ∧ d < 2 ^ 7] Int.toNat (d % 2 ^ 256)" -/
#guard_msgs in
#eval resolveText "pay" [("steps", "500")]
  [⟨"address", "asAbi"⟩, ⟨"bool", "asAbi"⟩, ⟨"bytes4", "asAbi"⟩, ⟨"int8", "asAbi"⟩, ⟨"uint256", "asAbi"⟩]

/-- info: "the ONCHAIN signature does not match the Solidity function (hint: expected set : uint256 -> ())" -/
#guard_msgs in #eval resolveText "set" [] [⟨"address", "asAbi"⟩, ⟨"()", "asAbi"⟩]

/-- info: "set returns (), not uint256 (hint: end the signature with -> ())" -/
#guard_msgs in #eval resolveText "set" [] [⟨"uint256", "asAbi"⟩, ⟨"uint256", "asAbi"⟩]

/-- info: "Box has no external function 'get' (hint: its external functions: set, pay)" -/
#guard_msgs in #eval resolveText "get" [] [⟨"()", "asAbi"⟩]

/-- info: "'exCPU' is a Plutus execution budget (hint: for the EVM, bound the execution with [steps: N])" -/
#guard_msgs in #eval resolveText "set" [("exCPU", "100")] [⟨"uint256", "asAbi"⟩, ⟨"()", "asAbi"⟩]

/-- info: "EVM version PlutusV3 is not modelled (hint: the machine models Cancun ([version: Cancun]))" -/
#guard_msgs in #eval resolveText "set" [("version", "PlutusV3")] [⟨"uint256", "asAbi"⟩, ⟨"()", "asAbi"⟩]

/-- info: "argument 1 of set: unknown encoding 'asData' (asAbi, asWord)" -/
#guard_msgs in #eval resolveText "set" [] [⟨"uint256", "asData"⟩, ⟨"()", "asAbi"⟩]

/-! ### Storage accessors -/

def u (bytes : Nat) : SolType := .value s!"uint{8 * bytes}" bytes "Nat" (8 * bytes)

/-- info: some ([], "Nat", "Sol.field (s.storage (0)) 20 1", [])
some ([], "Bool", "decide (Sol.field (s.storage (0)) 20 1 ≠ 0)", [])
some (["k1", "k2"], "Nat", "s.storage (Sol.mapSlot s.world (Sol.mapSlot s.world (3) k1) k2)", ["(64, [k1, 3])", "(64, [k2, Sol.mapSlot s.world (3) k1])"])
some (["k1"], "G", "⟨Sol.field (s.storage (Sol.structSlot (Sol.mapSlot s.world (2) k1) 0)) 0 16, Sol.field (s.storage (Sol.structSlot (Sol.mapSlot s.world (2) k1) 1)) 8 8⟩", ["(64, [k1, 2])"])
none
-/
#guard_msgs in
#eval show IO Unit from do
  for a in [accessor ⟨"x", 0, 20, u 1⟩,
       accessor ⟨"b", 0, 20, .value "bool" 1 "Bool" 8⟩,
       accessor ⟨"allowance", 3, 0, .mapping "m" (.value "address" 20 "Nat" 160) (.mapping "m" (.value "address" 20 "Nat" 160) (u 32))⟩,
       accessor ⟨"grants", 2, 0, .mapping "m" (.value "address" 20 "Nat" 160) (.struct "struct C.G" "G" 64 [("a", 0, 0, u 16), ("b", 1, 8, u 8)])⟩,
       accessor ⟨"name", 4, 0, .string "string"⟩] do
    IO.println (match a with
      | some (ps, t, b, hs) => s!"some ({repr ps}, {repr t}, {repr b}, {repr hs})"
      | none => "none")

/-! ### Values in counterexamples -/

/-- info: ["5", "2^256 - 1 (max uint256)", "2^256 - 3", "2^128", "2^160 - 1", "0x…0001", "msg.sender", "-1", "true"] -/
#guard_msgs in
#eval [fmtNat 5, fmtNat (2 ^ 256 - 1), fmtNat (2 ^ 256 - 3), fmtNat (2 ^ 128), fmtNat (2 ^ 160 - 1),
       fmtAddress 1, fmtAddress 7 [(7, "msg.sender")], fmtTyped 255 "int8", fmtTyped 1 "bool"]

def errorsModel : ContractModel :=
  { boxModel with errors := [⟨"Insufficient", "Insufficient(uint256)", 0xd1a1b2c3, [⟨"available", "uint256"⟩]⟩,
      ⟨"Error", "Error(string)", 0x08c379a0, [⟨"message", "string"⟩]⟩,
      ⟨"Panic", "Panic(uint256)", 0x4e487b71, [⟨"code", "uint256"⟩]⟩] }

def word (n : Nat) : String := hexDigits n 64

/-- info: reverts (no reason)
reverts with Insufficient(available: 7)
panics: arithmetic overflow or underflow
reverts: "no"
reverts with an unknown error (selector 0xdeadbeef)
-/
#guard_msgs in
#eval show IO Unit from do
  for r in [decodeRevert errorsModel "0x" [],
       decodeRevert errorsModel ("0xd1a1b2c3" ++ word 7) [],
       decodeRevert errorsModel ("0x4e487b71" ++ word 0x11) [],
       decodeRevert errorsModel ("0x08c379a0" ++ word 32 ++ word 2 ++ "6e6f" ++ String.mk (List.replicate 60 '0')) [],
       decodeRevert errorsModel "0xdeadbeef" []] do
    IO.println r

/-! ### Source maps -/

/-- info: (some 18, some 19, none) -/
#guard_msgs in
#eval show CoreM Unit from do
  let .ok a ← parse sample | throwError "parse"
  let (_, map) := propertyFile sample "M" "Box" ["Box"] a.properties[0]! 60
  IO.println (repr (locate map 9, locate map 10, locate map 1))

end Tests.UAL
