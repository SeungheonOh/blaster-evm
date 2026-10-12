import EvmBlaster.Instr
import EvmBlaster.Memory

/-!
# The EVM machine

A small-step interpreter for one message call into a contract, in the style of
PlutusCoreBlaster's CEK machine: `step` maps a machine state to the next one and
`run` iterates it under a fuel bound. Blaster executes it symbolically: the code and
program counter are concrete, the environment (`Env`) is symbolic, and `JUMPI` on a
symbolic condition splits the execution into an `if-then-else` of states.

## What is modelled

* All arithmetic, comparison, bitwise, hashing, context and stack instructions,
  memory (byte-precise), storage, transient storage, logs, `JUMP`/`JUMPI` with
  `JUMPDEST` validation, stack underflow/overflow, `RETURN`/`REVERT`/`INVALID`.
* `CALL` and `STATICCALL` to other contracts, whose outcome is answered by the oracle
  (`Oracle.call`); the value moves out of the contract's balance on success. Callees do
  not re-enter the contract (an assumption of the model).
* `KECCAK256` through the oracle's uninterpreted hash.

## What is not

* Gas: no instruction runs out of gas and `GAS` returns an arbitrary oracle value. The
  model therefore has more successful executions than the EVM, which keeps
  "every successful execution satisfies P" statements sound.
* `CREATE`, `CREATE2`, `CALLCODE`, `DELEGATECALL`, `SELFDESTRUCT`, `EXTCODECOPY`: they
  halt in `Result.unsupported`, which no property accepts (see `Result.onSuccess`).
-/

namespace Evm

/-- An emitted log. -/
structure LogEntry where
  topics : List Nat
  data : Slice
deriving Repr, Inhabited

inductive CallKind where
  | call | staticcall
deriving Repr, DecidableEq, Inhabited

/-- An outgoing call made by the contract. -/
structure CallRecord where
  kind : CallKind
  gas : Nat
  /-- The callee's address. -/
  to : Nat
  value : Nat
  input : Slice
  success : Bool
deriving Repr, Inhabited

/-- The machine state of the call frame being executed. -/
structure Frame where
  pc : Nat
  stack : List Nat
  memory : List MemWrite
  /-- Active memory size in bytes (a multiple of 32). -/
  msize : Nat
  /-- Storage writes over the initial storage `World.storage world`, newest first. -/
  storage : List (Nat × Nat)
  /-- Transient storage writes (transient storage starts at zero), newest first. -/
  transient : List (Nat × Nat)
  /-- The contract's balance. -/
  balance : Nat
  /-- Emitted logs, newest first. -/
  logs : List LogEntry
  /-- Outgoing calls, newest first. -/
  calls : List CallRecord
  callCount : Nat
  returndata : ReturnData
deriving Inhabited

/-- How an execution ends. -/
inductive Result where
  /-- `STOP` or `RETURN`: the frame's storage, balance, logs and calls take effect. -/
  | success (f : Frame) (output : Slice)
  /-- `REVERT`: every effect is discarded. -/
  | revert (output : Slice)
  /-- Exceptional halt (invalid instruction or jump, stack underflow/overflow, ...):
      every effect is discarded. -/
  | exception
  /-- The execution reached an instruction outside the modelled fragment. -/
  | unsupported (i : Instr)
  /-- The fuel bound was reached. -/
  | outOfFuel
deriving Inhabited

/-- Machine state. A running state carries the code and environment along with the
    frame so that it is always a constructor application, which lets Blaster unroll
    `run` (see `Box`). -/
inductive State where
  | running (c : Contract) (env : Env) (world : Query → Nat) (f : Frame)
  | halted (r : Result)

def maxStack : Nat := 1024

/-- Memory size after accessing `len` bytes at `off`. -/
def touch (msize off len : Nat) : Nat :=
  if len = 0 then msize else max msize ((off + len + 31) / 32 * 32)

/-- `n`-th element of a list. -/
def nth? : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth? xs n

/-- Replace the `n`-th element of a list. -/
def setNth (s : List Nat) (n : Nat) (v : Nat) : List Nat := go s n ⟨v⟩
 where
  go : List Nat → Nat → Box Nat → List Nat
  | [], _, _ => []
  | _ :: xs, 0, ⟨v⟩ => v :: xs
  | x :: xs, n + 1, v => x :: go xs n v

/-- `SWAPn`: exchange the top with the `n`-th element below it. -/
def swapTop (s : List Nat) (n : Nat) : Option (List Nat) :=
  match s with
  | [] => none
  | top :: rest =>
    match nth? rest (n - 1) with
    | some x => some (x :: setNth rest (n - 1) top)
    | none => none

/-- Split the first `n` elements of a list off. -/
def takeN : Nat → List Nat → Option (List Nat × List Nat)
  | 0, s => some ([], s)
  | _ + 1, [] => none
  | n + 1, x :: s =>
    match takeN n s with
    | some (xs, s') => some (x :: xs, s')
    | none => none

def evalBin : BinOp → Nat → Nat → Nat
  | .add => Word.add | .mul => Word.mul | .sub => Word.sub | .div => Word.div
  | .sdiv => Word.sdiv | .mod => Word.mod | .smod => Word.smod | .exp => Word.exp
  | .signextend => Word.signextend | .lt => Word.lt | .gt => Word.gt | .slt => Word.slt
  | .sgt => Word.sgt | .eq => Word.eq | .and => Word.and | .or => Word.or
  | .xor => Word.xor | .byte => Word.byte | .shl => Word.shl | .shr => Word.shr
  | .sar => Word.sar

def evalUn : UnOp → Nat → Nat
  | .iszero => Word.iszero | .not => Word.not

def evalTer : TerOp → Nat → Nat → Nat → Nat
  | .addmod => Word.addmod | .mulmod => Word.mulmod

section Step
variable (c : Contract) (env : Env) (world : Query → Nat)

def memCtx : MemCtx := ⟨env.msg.calldata, c.bytes, world⟩

def ctxValue (f : Frame) : CtxOp → Nat
  | .address => env.msg.address
  | .origin => env.tx.origin
  | .caller => env.msg.caller
  | .callvalue => env.msg.callvalue
  | .calldatasize => env.msg.calldata.size
  | .codesize => c.size
  | .gasprice => env.tx.gasprice
  | .returndatasize => f.returndata.size world
  | .coinbase => env.block.coinbase
  | .timestamp => env.block.timestamp
  | .number => env.block.number
  | .prevrandao => env.block.prevrandao
  | .gaslimit => env.block.gaslimit
  | .chainid => env.block.chainid
  | .selfbalance => f.balance
  | .basefee => env.block.basefee
  | .blobbasefee => env.block.blobbasefee
  | .pc => f.pc
  | .msize => f.msize
  | .gas => world (.gas f.pc)

def queryValue (f : Frame) (op : QueryOp) (a : Nat) : Nat :=
  match op with
  | .balance => if a % U160 = env.msg.address then f.balance else world (.balance (a % U160))
  | .extcodesize =>
    if a % U160 = env.msg.address then c.size else world (.extcodesize (a % U160))
  | .extcodehash => world (.extcodehash (a % U160))
  | .blockhash => world (.blockhash a)
  | .blobhash => world (.blobhash a)

/-- Push `v` and move to `pc'`, checking the stack limit. -/
def pushTo (f : Frame) (v : Nat) (pc' : Nat) : State :=
  if f.stack.length < maxStack then
    .running c env world { f with pc := pc', stack := v :: f.stack }
  else .halted .exception

/-- Continue at `d` if it is a `JUMPDEST`. -/
def jumpTo (f : Frame) (d : Nat) (s : List Nat) : State :=
  if c.code.fetch d = some .jumpdest then .running c env world { f with pc := d, stack := s }
  else .halted .exception

/-- An outgoing `CALL`/`STATICCALL`, answered by the world: the `i`-th call of the
    execution succeeds iff `world (.callSuccess i) ≠ 0` and returns the data
    `ReturnData.call i`. On success the value leaves the contract (unless the callee is
    the contract itself). -/
def doCall (f : Frame) (kind : CallKind) (gas to value inOff inLen outOff outLen : Nat)
    (s : List Nat) : State :=
  let msize := touch (touch f.msize inOff inLen) outOff outLen
  if f.balance < value then
    -- Insufficient balance: the call fails without reaching the callee.
    .running c env world
      { f with pc := f.pc + 1, stack := 0 :: s, msize := msize, returndata := ReturnData.empty }
  else
    let i := f.callCount
    let success := world (.callSuccess i) ≠ 0
    let output := ReturnData.call i
    let record : CallRecord :=
      { kind := kind, gas := gas, to := to % U160, value := value,
        input := ⟨f.memory, inOff, inLen⟩, success := decide success }
    .running c env world { f with
      pc := f.pc + 1
      stack := (if success then 1 else 0) :: s
      memory := if outLen = 0 then f.memory else .callOutput outOff outLen output :: f.memory
      msize := msize
      balance := if success ∧ to % U160 ≠ env.msg.address then f.balance - value else f.balance
      calls := record :: f.calls
      callCount := f.callCount + 1
      returndata := output }

/-- Execute instruction `i` in frame `f`. -/
def exec (f : Frame) (i : Instr) : State :=
  let next := f.pc + 1
  let cont : Frame → State := .running c env world
  let cx := memCtx c env world
  match i with
  | .stop => .halted (.success f Slice.empty)
  | .bin op =>
    match f.stack with
    | a :: b :: s => cont { f with pc := next, stack := evalBin op a b :: s }
    | _ => .halted .exception
  | .un op =>
    match f.stack with
    | a :: s => cont { f with pc := next, stack := evalUn op a :: s }
    | _ => .halted .exception
  | .ter op =>
    match f.stack with
    | a :: b :: n :: s => cont { f with pc := next, stack := evalTer op a b n :: s }
    | _ => .halted .exception
  | .ctx op => pushTo c env world f (ctxValue c env world f op) next
  | .query op =>
    match f.stack with
    | a :: s => cont { f with pc := next, stack := queryValue c env world f op a :: s }
    | _ => .halted .exception
  | .keccak256 =>
    match f.stack with
    | off :: len :: s =>
      let h := world (.keccak len (Memory.chunks cx f.memory ((len + 31) / 32) off len))
      cont { f with pc := next, stack := h :: s, msize := touch f.msize off len }
    | _ => .halted .exception
  | .calldataload =>
    match f.stack with
    | o :: s => cont { f with pc := next, stack := env.msg.calldata.load o :: s }
    | _ => .halted .exception
  | .calldatacopy =>
    match f.stack with
    | d :: src :: l :: s =>
      cont { f with
        pc := next, stack := s, msize := touch f.msize d l
        memory := if l = 0 then f.memory else .calldata d src l :: f.memory }
    | _ => .halted .exception
  | .codecopy =>
    match f.stack with
    | d :: src :: l :: s =>
      cont { f with
        pc := next, stack := s, msize := touch f.msize d l
        memory := if l = 0 then f.memory else .code d src l :: f.memory }
    | _ => .halted .exception
  | .returndatacopy =>
    match f.stack with
    | d :: src :: l :: s =>
      if f.returndata.size world < src + l then .halted .exception
      else
        let mem := if l = 0 then f.memory else .returndata d src l f.returndata :: f.memory
        cont { f with pc := next, stack := s, msize := touch f.msize d l, memory := mem }
    | _ => .halted .exception
  | .pop =>
    match f.stack with
    | _ :: s => cont { f with pc := next, stack := s }
    | _ => .halted .exception
  | .mload =>
    match f.stack with
    | o :: s =>
      cont { f with
        pc := next, stack := Memory.load cx f.memory o :: s
        msize := touch f.msize o 32 }
    | _ => .halted .exception
  | .mstore =>
    match f.stack with
    | o :: v :: s =>
      cont { f with
        pc := next, stack := s, memory := .word o v :: f.memory
        msize := touch f.msize o 32 }
    | _ => .halted .exception
  | .mstore8 =>
    match f.stack with
    | o :: v :: s =>
      cont { f with
        pc := next, stack := s, memory := .byte o (v % 256) :: f.memory
        msize := touch f.msize o 1 }
    | _ => .halted .exception
  | .sload =>
    match f.stack with
    | k :: s =>
      cont { f with pc := next, stack := Storage.read (World.storage world) f.storage k :: s }
    | _ => .halted .exception
  | .sstore =>
    match f.stack with
    | k :: v :: s => cont { f with pc := next, stack := s, storage := (k, v) :: f.storage }
    | _ => .halted .exception
  | .tload =>
    match f.stack with
    | k :: s => cont { f with pc := next, stack := Storage.read (fun _ => 0) f.transient k :: s }
    | _ => .halted .exception
  | .tstore =>
    match f.stack with
    | k :: v :: s => cont { f with pc := next, stack := s, transient := (k, v) :: f.transient }
    | _ => .halted .exception
  | .mcopy =>
    match f.stack with
    | d :: src :: l :: s =>
      cont { f with
        pc := next, stack := s, msize := touch (touch f.msize src l) d l
        memory := if l = 0 then f.memory else .mcopy d src l :: f.memory }
    | _ => .halted .exception
  | .jump =>
    match f.stack with
    | d :: s => jumpTo c env world f d s
    | _ => .halted .exception
  | .jumpi =>
    match f.stack with
    | d :: b :: s =>
      if b = 0 then cont { f with pc := next, stack := s } else jumpTo c env world f d s
    | _ => .halted .exception
  | .jumpdest => cont { f with pc := next }
  | .push n v => pushTo c env world f v (f.pc + 1 + n)
  | .dup n =>
    match nth? f.stack (n - 1) with
    | some v => pushTo c env world f v next
    | none => .halted .exception
  | .swap n =>
    match swapTop f.stack n with
    | some s => cont { f with pc := next, stack := s }
    | none => .halted .exception
  | .log n =>
    match f.stack with
    | off :: len :: s =>
      match takeN n s with
      | some (topics, s') =>
        cont { f with
          pc := next, stack := s', msize := touch f.msize off len
          logs := ⟨topics, ⟨f.memory, off, len⟩⟩ :: f.logs }
      | none => .halted .exception
    | _ => .halted .exception
  | .call =>
    match f.stack with
    | gas :: to :: value :: inOff :: inLen :: outOff :: outLen :: s =>
      doCall c env world f .call gas to value inOff inLen outOff outLen s
    | _ => .halted .exception
  | .staticcall =>
    match f.stack with
    | gas :: to :: inOff :: inLen :: outOff :: outLen :: s =>
      doCall c env world f .staticcall gas to 0 inOff inLen outOff outLen s
    | _ => .halted .exception
  | .ret =>
    match f.stack with
    | off :: len :: _ =>
      .halted (.success { f with msize := touch f.msize off len } ⟨f.memory, off, len⟩)
    | _ => .halted .exception
  | .revert =>
    match f.stack with
    | off :: len :: _ => .halted (.revert ⟨f.memory, off, len⟩)
    | _ => .halted .exception
  | .invalid => .halted .exception
  | .undefined _ => .halted .exception
  | .callcode | .delegatecall | .create | .create2 | .selfdestruct | .extcodecopy =>
    .halted (.unsupported i)

/-- One machine step. Running past the end of the code is `STOP`. -/
def step (f : Frame) : State :=
  match c.code.fetch f.pc with
  | some i => exec c env world f i
  | none => .halted (.success f Slice.empty)

end Step

/-- Iterate `step` at most `n` times. -/
def run (s : State) (n : Nat) : State :=
  match n, s with
  | _, .halted r => .halted r
  | 0, .running .. => .halted .outOfFuel
  | n + 1, .running c env world f => run (step c env world f) n

/-- The frame at the start of the call: the call value has been credited. -/
def Frame.init (env : Env) : Frame :=
  { pc := 0, stack := [], memory := [], msize := 0, storage := [], transient := [],
    balance := env.balance + env.msg.callvalue, logs := [], calls := [],
    callCount := 0, returndata := ReturnData.empty }

/-- Execute a message call to contract `c` in environment `env` and chain state `world`,
    with at most `fuel` steps. -/
def execute (c : Contract) (env : Env) (world : Query → Nat) (fuel : Nat) : Result :=
  match run (.running c env world (Frame.init env)) fuel with
  | .halted r => r
  | .running .. => .outOfFuel

end Evm
