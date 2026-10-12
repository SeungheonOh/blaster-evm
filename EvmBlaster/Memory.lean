import EvmBlaster.Env
import EvmBlaster.Instr

/-!
# Memory and storage

Memory is the list of writes performed so far, newest first, rather than a byte array.
A read walks the writes: an `MLOAD` at the exact offset of an `MSTORE` returns the stored
word, a write that does not overlap is skipped, and a partial overlap falls back to
assembling the word byte by byte (`byteAt`), which is the EVM's byte-array semantics.
Solidity's offsets are almost always literals during symbolic execution, so Blaster
resolves reads to the stored words without ever building byte expressions.

Copies (`CALLDATACOPY`, `CODECOPY`, `RETURNDATACOPY`, `MCOPY`) are recorded lazily as
writes that read their source on demand, so a copy of symbolic length is not unrolled.
-/

namespace Evm

inductive MemWrite where
  /-- `MSTORE off val`. -/
  | word (off : Nat) (val : Nat)
  /-- `MSTORE8 off val`, `val < 256`. -/
  | byte (off : Nat) (val : Nat)
  /-- `len` bytes of calldata from `src`, at `dst`. -/
  | calldata (dst src len : Nat)
  /-- `len` bytes of the executing code from `src`, at `dst`. -/
  | code (dst src len : Nat)
  /-- `len` bytes of return data `rd` from `src`, at `dst`. -/
  | returndata (dst src len : Nat) (rd : ReturnData)
  /-- `MCOPY`: `len` bytes of the memory as it was before this write, from `src`, at `dst`. -/
  | mcopy (dst src len : Nat)
  /-- The output area `[dst, dst + len)` of a call returning `rd`: its first `rd.size`
      bytes come from the return data, the rest keep their previous contents. (Recording
      the whole area, whose length is usually a literal, rather than the copied prefix,
      whose length is symbolic, keeps reads of it simple.) -/
  | callOutput (dst len : Nat) (rd : ReturnData)
deriving Repr, Inhabited

/-! Memory is the list of writes so far (`List MemWrite`), newest first; unwritten bytes
are zero. As for the world, the type is written out rather than abbreviated. -/

/-- What reading memory needs besides the writes: the sources of lazy copies.
    An `inductive` rather than a `structure` (see `Box`). -/
inductive MemCtx where
  | mk (calldata : Calldata) (code : ByteTree) (world : Query → Nat)

def MemCtx.calldata : MemCtx → Calldata
  | .mk cd _ _ => cd

def MemCtx.code : MemCtx → ByteTree
  | .mk _ code _ => code

def MemCtx.world : MemCtx → Query → Nat
  | .mk _ _ w => w

namespace Memory

/-- `[d, d + l)` and `[a, a + 32)` do not intersect. -/
abbrev Disjoint32 (d l a : Nat) : Prop := d + l ≤ a ∨ a + 32 ≤ d

/-- `[a, a + 32)` is inside `[d, d + l)`. -/
abbrev Covers32 (d l a : Nat) : Prop := d ≤ a ∧ a + 32 ≤ d + l

/-- Byte `i` of memory. -/
def byteAt (cx : MemCtx) (mem : List MemWrite) (i : Nat) : Nat := go mem ⟨i⟩
 where
  go : List MemWrite → Box Nat → Nat
  | [], _ => 0
  | .word o v :: rest, ⟨i⟩ => if o ≤ i ∧ i < o + 32 then Word.byteOf v (i - o) else go rest ⟨i⟩
  | .byte o v :: rest, ⟨i⟩ => if i = o then v else go rest ⟨i⟩
  | .calldata d s l :: rest, ⟨i⟩ =>
    if d ≤ i ∧ i < d + l then cx.calldata.byteAt (s + (i - d)) else go rest ⟨i⟩
  | .code d s l :: rest, ⟨i⟩ =>
    if d ≤ i ∧ i < d + l then cx.code.get (s + (i - d)) else go rest ⟨i⟩
  | .returndata d s l rd :: rest, ⟨i⟩ =>
    if d ≤ i ∧ i < d + l then rd.byteAt cx.world (s + (i - d)) else go rest ⟨i⟩
  | .mcopy d s l :: rest, ⟨i⟩ =>
    if d ≤ i ∧ i < d + l then go rest ⟨s + (i - d)⟩ else go rest ⟨i⟩
  | .callOutput d l rd :: rest, ⟨i⟩ =>
    if d ≤ i ∧ i < d + l ∧ i - d < rd.size cx.world then rd.byteAt cx.world (i - d)
    else go rest ⟨i⟩

/-- The region `[dst, dst + len)` a write covers. -/
def _root_.Evm.MemWrite.dst : MemWrite → Nat
  | .word o _ | .byte o _ => o
  | .calldata d _ _ | .code d _ _ | .returndata d _ _ _ | .mcopy d _ _ | .callOutput d _ _ => d

def _root_.Evm.MemWrite.len : MemWrite → Nat
  | .word _ _ => 32
  | .byte _ _ => 1
  | .calldata _ _ l | .code _ _ l | .returndata _ _ l _ | .mcopy _ _ l | .callOutput _ l _ => l

/-- How a write that intersects `[a, a + 32)` answers a 32-byte read at `a`. -/
inductive Direct where
  /-- The write provides the word. -/
  | value (v : Nat)
  /-- An `MCOPY` covering the word: read the older memory at this address instead. -/
  | redirect (a : Nat)
  /-- Partial overlap: assemble byte by byte. -/
  | bytes

def direct (cx : MemCtx) (w : MemWrite) (a : Nat) : Direct :=
  match w with
  | .word o v => if o = a then .value v else .bytes
  | .byte .. | .code .. => .bytes
  | .calldata d s l => if Covers32 d l a then .value (cx.calldata.load (s + (a - d))) else .bytes
  | .returndata d s l rd =>
    if Covers32 d l a then .value (rd.load cx.world (s + (a - d))) else .bytes
  | .mcopy d s l => if Covers32 d l a then .redirect (s + (a - d)) else .bytes
  | .callOutput d l rd =>
    if Covers32 d l a ∧ a - d + 32 ≤ rd.size cx.world then .value (rd.load cx.world (a - d))
    else .bytes

/-- `MLOAD a`: the 32 bytes at `a`. Writes not intersecting the word are skipped; an
    `MSTORE` at exactly `a` (or a copy covering the word) answers directly; any other
    overlap is assembled byte by byte (`byteAt`). That fallback is linear in the number of
    writes even when offsets are symbolic (e.g. after a dynamic allocation), which matters
    more in practice than compact terms for overlaps at literal offsets. (The per-write
    cases live in `direct` so that the recursion has a single case, which keeps Lean's
    equation generator cheap.) -/
def load (cx : MemCtx) (mem : List MemWrite) (a : Nat) : Nat := go mem ⟨a⟩
 where
  go : List MemWrite → Box Nat → Nat
  | [], _ => 0
  | w :: rest, ⟨a⟩ =>
    if Disjoint32 w.dst w.len a then go rest ⟨a⟩
    else
      match direct cx w a with
      | .value v => v
      | .redirect a' => go rest ⟨a'⟩
      | .bytes => Word.assemble (byteAt cx (w :: rest)) a

/-- The `n` 32-byte chunks of the `len` bytes at `off` (a partial last chunk is
    zero-padded), with `n = ⌈len / 32⌉`. -/
def chunks (cx : MemCtx) (mem : List MemWrite) (n off len : Nat) : List Nat := go n ⟨(off, len)⟩
 where
  go : Nat → Box (Nat × Nat) → List Nat
  | 0, _ => []
  | n + 1, ⟨(off, len)⟩ => Word.keepBytes len (load cx mem off) :: go n ⟨(off + 32, len - 32)⟩

end Memory

/-- A region of memory, frozen at the time it was produced (log data, call input,
    return data). -/
structure Slice where
  mem : List MemWrite
  off : Nat
  len : Nat
deriving Repr, Inhabited

namespace Slice

def empty : Slice := ⟨[], 0, 0⟩

/-- The `i`-th 32-byte word of the slice (`i = 0` is the first word). -/
def word (cx : MemCtx) (s : Slice) (i : Nat) : Nat :=
  Word.keepBytes (s.len - 32 * i) (Memory.load cx s.mem (s.off + 32 * i))

end Slice

/-! Storage is the list of writes so far (`List (Nat × Nat)`: `(key, value)`, newest
first) over an initial storage. -/

/-- The value of key `k`. -/
def Storage.read (init : Nat → Nat) (st : List (Nat × Nat)) (k : Nat) : Nat := go st ⟨k⟩
 where
  go : List (Nat × Nat) → Box Nat → Nat
  | [], ⟨k⟩ => init k
  | (k', v) :: rest, ⟨k⟩ => if k = k' then v else go rest ⟨k⟩

end Evm
