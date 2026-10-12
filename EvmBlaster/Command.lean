import Lean
import EvmBlaster.Instr

/-!
# Importing bytecode

`#evm_contract Name "0x6080..."` and `#evm_contract_file Name "path/to/X.bin-runtime"`
decode runtime bytecode at elaboration time and define `Name : Evm.Contract`.
-/

namespace Evm
open Lean Elab Command

deriving instance ToExpr for Contract

def defineContract (name : Name) (hex : String) (ref : Syntax) : CommandElabM Unit := do
  let bytes ← match parseHex hex with
    | .ok b => pure b
    | .error e => throwErrorAt ref m!"invalid bytecode: {e}"
  let c := Contract.ofBytes bytes
  let declName := (← getCurrNamespace) ++ name
  let decl := Declaration.defnDecl {
    name := declName, levelParams := [], type := mkConst ``Contract,
    value := toExpr c, hints := .abbrev, safety := .safe }
  -- The code tree is a large constant; compiling it (for concrete `#eval` runs) recurses
  -- past the default depth limit.
  withScope (fun sc => { sc with opts := maxRecDepth.set sc.opts 100000 }) <|
    liftCoreM <| withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := 100000 }) <|
      addAndCompile decl

syntax (name := evmContract) "#evm_contract " ident str : command
syntax (name := evmContractFile) "#evm_contract_file " ident str : command

@[command_elab evmContract]
def elabEvmContract : CommandElab := fun stx => do
  let some hex := stx[2].isStrLit? | throwUnsupportedSyntax
  defineContract stx[1].getId hex stx[2]

@[command_elab evmContractFile]
def elabEvmContractFile : CommandElab := fun stx => do
  let some path := stx[2].isStrLit? | throwUnsupportedSyntax
  let hex ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok s => pure s
    | .error e => throwErrorAt stx[2] m!"cannot read '{path}': {e}"
  defineContract stx[1].getId hex stx[2]

end Evm
