import EvmBlaster.Word

/-!
# Execution environment and chain state

The EVM is not a pure function of the bytecode: an execution reads its message, the
transaction and the block (`Env`, first-order data), and queries chain state: its own
storage, other accounts, block hashes, keccak256, and the outcome of the calls it makes.
All chain-state reads go through a single function `world : Query → Nat`. Theorems
quantify over every `Env` and every `World`; assumptions about the chain state are
hypotheses about the world.

(The world is one function on a query datatype rather than a structure of functions
because Blaster translates function variables to SMT, but not yet applications of
function-typed structure fields.)
-/

namespace Evm

/-- Calldata: a byte string of `size` bytes, viewed as a 4-byte selector followed by
    32-byte words (missing bytes read as zero). Every byte string has this form, so a
    theorem over all `Calldata` covers every possible input, including truncated or
    oversized calldata. -/
structure Calldata where
  /-- Bytes `0..3`, big-endian. -/
  selector : Nat
  /-- Bytes from offset 4, in 32-byte big-endian words. -/
  args : List Nat
  /-- Size in bytes. -/
  size : Nat
deriving Repr, Inhabited

namespace Calldata

/-- No calldata (a plain transfer). -/
def empty : Calldata := ⟨0, [], 0⟩

/-- ABI calldata: a function selector followed by 32-byte arguments. -/
def ofAbi (selector : Nat) (args : List Nat) : Calldata := ⟨selector, args, 4 + 32 * args.length⟩

/-- The calldata of a raw byte string (zero-padded to the selector and to whole words). -/
def ofBytes (bs : Array UInt8) : Calldata :=
  let byte (i : Nat) : Nat := (bs.getD i 0).toNat
  let selector := byte 0 * 2 ^ 24 + byte 1 * 2 ^ 16 + byte 2 * 2 ^ 8 + byte 3
  let nwords := (bs.size - 4 + 31) / 32
  let word (k : Nat) : Nat :=
    (List.range 32).foldl (fun acc j => acc * 256 + byte (4 + 32 * k + j)) 0
  ⟨selector, (List.range nwords).map word, bs.size⟩

/-- Byte `i` of the calldata. -/
def byteAt (cd : Calldata) (i : Nat) : Nat :=
  if i < 4 then (cd.selector / 2 ^ (8 * (3 - i))) % 256
  else Word.byteOf (cd.args.getD ((i - 4) / 32) 0) ((i - 4) % 32)

/-- `CALLDATALOAD o`: the 32 bytes at `o`, from at most two components: the selector and
    the first argument word when `o < 4`; otherwise the last `32 - d` bytes of argument
    word `k` followed by the first `d` bytes of word `k + 1`, where `o = 4 + 32 k + d`.
    (One division and modulo per component rather than one per byte.) -/
def load (cd : Calldata) (o : Nat) : Nat :=
  if o = 0 then cd.selector * 2 ^ 224 + cd.args.getD 0 0 / 2 ^ 32
  else if o < 4 then
    (cd.selector % 2 ^ (8 * (4 - o))) * 2 ^ (8 * (28 + o))
      + cd.args.getD 0 0 / 2 ^ (8 * (4 - o))
  else
    let k := (o - 4) / 32
    let d := (o - 4) % 32
    if d = 0 then cd.args.getD k 0
    else
      (cd.args.getD k 0 % 2 ^ (8 * (32 - d))) * 2 ^ (8 * d)
        + cd.args.getD (k + 1) 0 / 2 ^ (8 * (32 - d))

/-- Every element is a word. (Recursive rather than `∀ a ∈ args`: Blaster does not
    support inductive predicates such as `List.Mem`.) -/
def AllWords : List Nat → Prop
  | [] => True
  | a :: as => a < U256 ∧ AllWords as

/-- The components are words and the size is realistic.

    The bytes at or beyond `size` are *not* required to be zero: the model then also
    contains executions in which reads past the end of the calldata see nonzero bytes.
    Every real calldata is still represented (with zero padding), so properties of all
    executions remain sound for the EVM; requiring the padding would only make the
    SMT queries harder (it relates `size` to the length of a symbolic list). -/
def WF (cd : Calldata) : Prop :=
  cd.selector < 2 ^ 32 ∧ AllWords cd.args ∧ cd.size < 2 ^ 32

end Calldata

/-- A question an execution can ask about the chain. -/
inductive Query where
  /-- The executing contract's storage at `key`, at the start of the call. -/
  | storage (key : Nat)
  /-- keccak256 of the `len`-byte string whose 32-byte chunks are `chunks` (a partial
      last chunk is zero-padded). -/
  | keccak (len : Nat) (chunks : List Nat)
  /-- `BALANCE` of an account other than the executing one. -/
  | balance (addr : Nat)
  | extcodesize (addr : Nat)
  | extcodehash (addr : Nat)
  | blockhash (number : Nat)
  | blobhash (index : Nat)
  /-- The value of `GAS` at program counter `pc` (gas is not modelled). -/
  | gas (pc : Nat)
  /-- Whether the `i`-th outgoing call of the execution succeeds (nonzero). -/
  | callSuccess (i : Nat)
  /-- The size in bytes of the return data of the `i`-th outgoing call. -/
  | returnSize (i : Nat)
  /-- The `j`-th 32-byte word of the return data of the `i`-th outgoing call. -/
  | returnWord (i j : Nat)
deriving Repr, Inhabited

/-! ### The world

The chain state an execution depends on is a function `world : Query → Nat` answering
every query. An execution is a function of its `Env` and its world, and theorems quantify
over both. Assumptions about the chain state are hypotheses constraining the world, e.g.
`World.KeccakInjective world` or "the `0`-th call succeeds". Outgoing calls are answered by
the world rather than executed: callees do not re-enter the contract and do not send Ether
back to it during the call.

The type is written out as `Query → Nat` everywhere rather than through an abbreviation:
Blaster does not unfold abbreviations when analysing the type of a function variable.
The helpers below live in the `World` namespace. -/

namespace World

/-- The executing contract's storage at the start of the call. -/
def storage (w : Query → Nat) (k : Nat) : Nat := w (.storage k)

/-- The world `w` in which the executing contract's storage is `σ`. -/
def withStorage (w : Query → Nat) (σ : Nat → Nat) : Query → Nat
  | .storage k => σ k
  | q => w q

/-- Every answer is a word. -/
def WF (w : Query → Nat) : Prop := ∀ q, w q < U256

/-- Idealised collision resistance of keccak256 on inputs of the same length. -/
def KeccakInjective (w : Query → Nat) : Prop :=
  ∀ n ws ws', w (.keccak n ws) = w (.keccak n ws') → ws = ws'

/-- Hashes never land below `bound`, i.e. on the slots of plain state variables. -/
def KeccakAbove (w : Query → Nat) (bound : Nat) : Prop :=
  ∀ n ws, bound ≤ w (.keccak n ws)

/-- Hashes of distinct inputs are at least `d` apart, and at least `d` below `2^256`: the
    `d` consecutive slots of a struct stored at a hash (Solidity's layout for structs in
    mappings) never meet another hashed slot, and never wrap around. -/
def KeccakSpread (w : Query → Nat) (d : Nat) : Prop :=
  (∀ n ws n' ws', (n ≠ n' ∨ ws ≠ ws') →
    w (.keccak n ws) + d ≤ w (.keccak n' ws') ∨ w (.keccak n' ws') + d ≤ w (.keccak n ws)) ∧
  ∀ n ws, w (.keccak n ws) + d ≤ U256

end World

/-- Return data: empty, or that of the `i`-th outgoing call. -/
inductive ReturnData where
  | empty
  | call (i : Nat)
deriving Repr, Inhabited

namespace ReturnData

def size (w : Query → Nat) : ReturnData → Nat
  | .empty => 0
  | .call i => w (.returnSize i)

def byteAt (w : Query → Nat) (rd : ReturnData) (k : Nat) : Nat :=
  match rd with
  | .empty => 0
  | .call i =>
    if k < w (.returnSize i) then Word.byteOf (w (.returnWord i (k / 32))) (k % 32) else 0

def load (w : Query → Nat) (rd : ReturnData) (o : Nat) : Nat :=
  match rd with
  | .empty => 0
  | .call i =>
    if o + 32 ≤ w (.returnSize i) then
      let k := o / 32
      let d := o % 32
      if d = 0 then w (.returnWord i k)
      else (w (.returnWord i k) % 2 ^ (8 * (32 - d))) * 2 ^ (8 * d)
        + w (.returnWord i (k + 1)) / 2 ^ (8 * (32 - d))
    else Word.assemble (byteAt w rd) o

end ReturnData

/-- Block context. -/
structure Block where
  coinbase : Nat
  timestamp : Nat
  number : Nat
  prevrandao : Nat
  gaslimit : Nat
  chainid : Nat
  basefee : Nat
  blobbasefee : Nat
deriving Repr, Inhabited

/-- Transaction context. -/
structure Tx where
  origin : Nat
  gasprice : Nat
deriving Repr, Inhabited

/-- The message calling the contract. -/
structure Msg where
  /-- The address of the executing contract. -/
  address : Nat
  caller : Nat
  callvalue : Nat
  calldata : Calldata
deriving Repr, Inhabited

/-- The context of an execution (first-order data; the chain state is the `World`). -/
structure Env where
  block : Block
  tx : Tx
  msg : Msg
  /-- The executing contract's balance before the call value is credited. -/
  balance : Nat
deriving Repr, Inhabited

/-- The same environment with other calldata (e.g. to compare two calls). -/
def Env.withCalldata (env : Env) (cd : Calldata) : Env :=
  { env with msg := { env.msg with calldata := cd } }

/-- Assumptions every execution relies on: the inputs are words, addresses are 160 bits,
    and crediting the call value does not overflow the balance. -/
def Env.WF (env : Env) : Prop :=
  env.block.coinbase < U160 ∧ env.block.timestamp < U256 ∧ env.block.number < U256 ∧
  env.block.prevrandao < U256 ∧ env.block.gaslimit < U256 ∧ env.block.chainid < U256 ∧
  env.block.basefee < U256 ∧ env.block.blobbasefee < U256 ∧
  env.tx.origin < U160 ∧ env.tx.gasprice < U256 ∧
  env.msg.address < U160 ∧ env.msg.caller < U160 ∧ env.msg.callvalue < U256 ∧
  env.msg.calldata.WF ∧ env.balance + env.msg.callvalue < U256

end Evm
