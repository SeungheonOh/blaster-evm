import Lean
import EvmBlaster.Word

/-!
# EVM instructions, decoding and code layout

Bytecode is decoded once, at elaboration time, into a balanced binary search tree from
program counters to instructions (`Code`). During symbolic execution the program counter
is always a literal, so Blaster resolves every `Code.fetch` by constant folding in
`O(log n)` comparisons. Only instruction starts are keys of the tree: a jump into PUSH
data finds no `JUMPDEST` and is an exceptional halt, as in the EVM.
-/

namespace Evm
open Lean

/-- Binary operators `a op b`, `a` being the top of the stack. -/
inductive BinOp where
  | add | mul | sub | div | sdiv | mod | smod | exp | signextend
  | lt | gt | slt | sgt | eq | and | or | xor | byte | shl | shr | sar
deriving Repr, DecidableEq, Inhabited, ToExpr

/-- Unary operators. -/
inductive UnOp where
  | iszero | not
deriving Repr, DecidableEq, Inhabited, ToExpr

/-- Ternary operators. -/
inductive TerOp where
  | addmod | mulmod
deriving Repr, DecidableEq, Inhabited, ToExpr

/-- Instructions that push a value read from the execution context. -/
inductive CtxOp where
  | address | origin | caller | callvalue | calldatasize | codesize | gasprice
  | returndatasize | coinbase | timestamp | number | prevrandao | gaslimit | chainid
  | selfbalance | basefee | blobbasefee | pc | msize | gas
deriving Repr, DecidableEq, Inhabited, ToExpr

/-- Instructions that replace the top of the stack by a chain-state query. -/
inductive QueryOp where
  | balance | extcodesize | extcodehash | blockhash | blobhash
deriving Repr, DecidableEq, Inhabited, ToExpr

inductive Instr where
  | stop
  | bin (op : BinOp)
  | un (op : UnOp)
  | ter (op : TerOp)
  | ctx (op : CtxOp)
  | query (op : QueryOp)
  | keccak256
  | calldataload | calldatacopy | codecopy | extcodecopy | returndatacopy
  | pop | mload | mstore | mstore8 | sload | sstore | tload | tstore | mcopy
  | jump | jumpi | jumpdest
  /-- `push n v`: `PUSHn` (`n ≤ 32`, `PUSH0` is `push 0 0`) pushing `v`. -/
  | push (n : Nat) (v : Nat)
  /-- `dup n`: `DUPn`, `1 ≤ n ≤ 16`. -/
  | dup (n : Nat)
  /-- `swap n`: `SWAPn`, `1 ≤ n ≤ 16`. -/
  | swap (n : Nat)
  /-- `log n`: `LOGn`, `n ≤ 4`. -/
  | log (n : Nat)
  | call | staticcall | callcode | delegatecall | create | create2 | selfdestruct
  | ret | revert | invalid
  /-- An undefined opcode (exceptional halt). -/
  | undefined (op : Nat)
deriving Repr, DecidableEq, Inhabited, ToExpr

/-- Decode one opcode byte. PUSH immediates are handled by `decode`. -/
def opcodeToInstr (op : Nat) : Instr :=
  match op with
  | 0x00 => .stop
  | 0x01 => .bin .add | 0x02 => .bin .mul | 0x03 => .bin .sub | 0x04 => .bin .div
  | 0x05 => .bin .sdiv | 0x06 => .bin .mod | 0x07 => .bin .smod
  | 0x08 => .ter .addmod | 0x09 => .ter .mulmod
  | 0x0a => .bin .exp | 0x0b => .bin .signextend
  | 0x10 => .bin .lt | 0x11 => .bin .gt | 0x12 => .bin .slt | 0x13 => .bin .sgt
  | 0x14 => .bin .eq | 0x15 => .un .iszero
  | 0x16 => .bin .and | 0x17 => .bin .or | 0x18 => .bin .xor | 0x19 => .un .not
  | 0x1a => .bin .byte | 0x1b => .bin .shl | 0x1c => .bin .shr | 0x1d => .bin .sar
  | 0x20 => .keccak256
  | 0x30 => .ctx .address | 0x31 => .query .balance | 0x32 => .ctx .origin
  | 0x33 => .ctx .caller | 0x34 => .ctx .callvalue | 0x35 => .calldataload
  | 0x36 => .ctx .calldatasize | 0x37 => .calldatacopy | 0x38 => .ctx .codesize
  | 0x39 => .codecopy | 0x3a => .ctx .gasprice | 0x3b => .query .extcodesize
  | 0x3c => .extcodecopy | 0x3d => .ctx .returndatasize | 0x3e => .returndatacopy
  | 0x3f => .query .extcodehash
  | 0x40 => .query .blockhash | 0x41 => .ctx .coinbase | 0x42 => .ctx .timestamp
  | 0x43 => .ctx .number | 0x44 => .ctx .prevrandao | 0x45 => .ctx .gaslimit
  | 0x46 => .ctx .chainid | 0x47 => .ctx .selfbalance | 0x48 => .ctx .basefee
  | 0x49 => .query .blobhash | 0x4a => .ctx .blobbasefee
  | 0x50 => .pop | 0x51 => .mload | 0x52 => .mstore | 0x53 => .mstore8
  | 0x54 => .sload | 0x55 => .sstore | 0x56 => .jump | 0x57 => .jumpi
  | 0x58 => .ctx .pc | 0x59 => .ctx .msize | 0x5a => .ctx .gas | 0x5b => .jumpdest
  | 0x5c => .tload | 0x5d => .tstore | 0x5e => .mcopy | 0x5f => .push 0 0
  | 0xf0 => .create | 0xf1 => .call | 0xf2 => .callcode | 0xf3 => .ret
  | 0xf4 => .delegatecall | 0xf5 => .create2 | 0xfa => .staticcall
  | 0xfd => .revert | 0xfe => .invalid | 0xff => .selfdestruct
  | op =>
    if 0x80 ≤ op ∧ op ≤ 0x8f then .dup (op - 0x7f)
    else if 0x90 ≤ op ∧ op ≤ 0x9f then .swap (op - 0x8f)
    else if 0xa0 ≤ op ∧ op ≤ 0xa4 then .log (op - 0xa0)
    else .undefined op

/-- Big-endian value of `n` bytes of `code` starting at `i` (missing bytes are zero). -/
def readImmediate (code : Array UInt8) (i n : Nat) : Nat :=
  (List.range n).foldl (fun acc j => acc * 256 + (code.getD (i + j) 0).toNat) 0

/-- Decode bytecode into `(pc, instruction)` pairs, in increasing `pc` order. -/
def decode (code : Array UInt8) : List (Nat × Instr) :=
  go code.size 0 []
 where
  go : Nat → Nat → List (Nat × Instr) → List (Nat × Instr)
  | 0, _, acc => acc.reverse
  | fuel + 1, pc, acc =>
    if pc < code.size then
      let op := (code.getD pc 0).toNat
      if 0x60 ≤ op ∧ op ≤ 0x7f then
        let n := op - 0x5f
        go fuel (pc + 1 + n) ((pc, .push n (readImmediate code (pc + 1) n)) :: acc)
      else go fuel (pc + 1) ((pc, opcodeToInstr op) :: acc)
    else acc.reverse

/-- Program code as a balanced binary search tree keyed by program counter. -/
inductive Code where
  | leaf
  | node (left : Code) (pc : Nat) (instr : Instr) (right : Code)
deriving Repr, Inhabited, ToExpr

/-- The instruction starting at `pc`, if any. -/
def Code.fetch (code : Code) (pc : Nat) : Option Instr := go code ⟨pc⟩
 where
  go : Code → Box Nat → Option Instr
  | .leaf, _ => none
  | .node l k i r, ⟨pc⟩ => if pc < k then go l ⟨pc⟩ else if pc = k then some i else go r ⟨pc⟩

/-- Build a balanced tree from instructions sorted by `pc`. -/
def Code.ofSorted (xs : Array (Nat × Instr)) : Code :=
  go xs.size 0 xs.size
 where
  go : Nat → Nat → Nat → Code
  | 0, _, _ => .leaf
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let (pc, i) := xs[mid]!
      .node (go fuel lo mid) pc i (go fuel (mid + 1) hi)
    else .leaf

/-- Bytes indexed by position, as a balanced binary search tree (as for `Code`, a list
    would be as deep as the bytecode is long). Missing positions read as zero. -/
inductive ByteTree where
  | leaf
  | node (left : ByteTree) (i : Nat) (b : Nat) (right : ByteTree)
deriving Repr, Inhabited, ToExpr

def ByteTree.get (t : ByteTree) (i : Nat) : Nat := go t ⟨i⟩
 where
  go : ByteTree → Box Nat → Nat
  | .leaf, _ => 0
  | .node l k b r, ⟨i⟩ => if i < k then go l ⟨i⟩ else if i = k then b else go r ⟨i⟩

def ByteTree.ofArray (xs : Array Nat) : ByteTree :=
  go xs.size 0 xs.size
 where
  go : Nat → Nat → Nat → ByteTree
  | 0, _, _ => .leaf
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      .node (go fuel lo mid) mid xs[mid]! (go fuel (mid + 1) hi)
    else .leaf

/-- A deployed contract: its runtime code. -/
structure Contract where
  code : Code
  /-- The raw bytecode, for `CODECOPY`. -/
  bytes : ByteTree
  size : Nat

/-- Parse a hex string (optionally `0x`-prefixed, whitespace ignored) into bytes.
    Iterative: `#evm_contract` runs it in Lean's interpreter, which bounds the call depth. -/
def parseHex (s : String) : Except String (Array UInt8) := do
  let s := s.trim
  let s := if s.startsWith "0x" then s.drop 2 else s
  let digits := (s.toList.filter (fun c => !c.isWhitespace)).toArray
  if digits.size % 2 != 0 then throw "odd number of hex digits"
  let hexVal (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"invalid hex digit '{c}'"
  let mut out := Array.mkEmpty (digits.size / 2)
  for i in [0:digits.size / 2] do
    out := out.push (UInt8.ofNat ((← hexVal digits[2 * i]!) * 16 + (← hexVal digits[2 * i + 1]!)))
  return out

def Contract.ofBytes (code : Array UInt8) : Contract :=
  { code := Code.ofSorted (decode code).toArray
    bytes := ByteTree.ofArray (code.map UInt8.toNat)
    size := code.size }

end Evm
