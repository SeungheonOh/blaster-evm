import Std.Data.HashSet
import Conformance.Support

/-!
# Conformance: a lower bound on gas

The machine does not model gas. The test suites do: some executions are *expected* to
run out of gas, and their expected effects are those of an exceptional halt. To tell
these cases apart from real disagreements, the runner adds up, along the machine's own
execution, a lower bound on the gas each instruction is charged before it runs. When the
bound exceeds the gas available, the EVM certainly ran out of gas on that execution.

For Cancun the bound follows the fork's rules for the instructions the machine runs,
including the EIP-2929 surcharges for the first access to an account or storage slot.
For the Constantinople VM tests it uses the minimum of the two forks' costs, e.g. 100 for
`SLOAD` (a warm read in Cancun, 200 in Constantinople). The bound is used for
classification only: the machine's semantics never depends on it.
-/

namespace Conformance
open Evm

/-- The cost of `msize` bytes of active memory (`msize` a multiple of 32). -/
def memCost (msize : Nat) : Nat := let w := msize / 32; 3 * w + w * w / 512

/-- The number of 32-byte words of `len` bytes. -/
def words (len : Nat) : Nat := (len + 31) / 32

/-- The number of bytes of `e` (the `EXP` exponent cost unit). -/
def byteLen (e : Nat) : Nat := if e == 0 then 0 else Nat.log2 e / 8 + 1

/-- What the gas bound needs to know about the chain. -/
structure GasCtx where
  /-- Storage at the start of the transaction (the "original" values of EIP-2200). -/
  original : Nat → Nat
  /-- Whether an account is dead (EIP-161) before the transaction. -/
  dead : Nat → Bool
  /-- Cancun rules: EIP-2929 cold-access costs and the EIP-2200 `SSTORE` sentry. Without
      them (Constantinople), accesses cost what a warm access costs in Cancun, which is
      less than in Constantinople. -/
  cancun : Bool

/-- The accounts and storage slots (of the executing contract) accessed so far. -/
structure Warm where
  addrs : Std.HashSet Nat := {}
  slots : Std.HashSet Nat := {}
deriving Inhabited

/-- What an instruction is charged: `required` must be available before it runs, `net`
    is consumed (a call's stipend can come back). -/
structure Charge where
  required : Nat
  net : Nat
  warm : Warm

/-- `SSTORE` of `v` over the current value `cur`, `orig` at the start of the
    transaction, for a warm slot (EIP-2200 with EIP-2929 costs; at least as much in
    earlier forks). -/
def sstoreCost (orig cur v : Nat) : Nat :=
  if v == cur then 100
  else if orig == cur then (if orig == 0 then 20000 else 2900)
  else 100

/-- A lower bound on the gas charged for executing `i` in frame `f`. Missing stack
    arguments read as zero (the instruction then halts exceptionally anyway). -/
def charge (g : GasCtx) (w : Warm) (f : Frame) (i : Instr) : Charge :=
  let arg (n : Nat) := (nth? f.stack n).getD 0
  let plain (n : Nat) : Charge := ⟨n, n, w⟩
  -- memory expansion for the regions `rs`
  let expand (rs : List (Nat × Nat)) :=
    memCost (rs.foldl (fun m (off, len) => touch m off len) f.msize) - memCost f.msize
  -- access to an account: 100 when warm, 2600 when cold (Cancun)
  let account (a : Nat) : Nat × Warm :=
    let a := a % U160
    if !g.cancun || w.addrs.contains a then (100, w) else (2600, { w with addrs := w.addrs.insert a })
  -- the cold surcharge of a storage slot (Cancun)
  let slot (k : Nat) : Nat × Warm :=
    if !g.cancun || w.slots.contains k then (0, w) else (2100, { w with slots := w.slots.insert k })
  match i with
  | .stop | .invalid | .undefined _ => plain 0
  | .ret | .revert => plain (expand [(arg 0, arg 1)])
  | .jumpdest => plain 1
  | .ctx .selfbalance => plain 5
  | .ctx _ => plain 2
  | .push 0 _ => plain 2
  | .push .. | .dup _ | .swap _ | .un _ | .calldataload => plain 3
  | .pop => plain 2
  | .bin op =>
    match op with
    | .mul | .div | .sdiv | .mod | .smod | .signextend => plain 5
    | .exp => plain (10 + 50 * byteLen (arg 1))
    | _ => plain 3
  | .ter _ => plain 8
  | .query .blockhash => plain 20
  | .query .blobhash => plain 3
  | .query _ => let (n, w) := account (arg 0); ⟨n, n, w⟩
  | .keccak256 => plain (30 + 6 * words (arg 1) + expand [(arg 0, arg 1)])
  | .calldatacopy | .codecopy | .returndatacopy =>
    plain (3 + 3 * words (arg 2) + expand [(arg 0, arg 2)])
  | .extcodecopy =>
    let (n, w) := account (arg 0)
    let n := n + 3 * words (arg 3) + expand [(arg 1, arg 3)]
    ⟨n, n, w⟩
  | .mcopy => plain (3 + 3 * words (arg 2) + expand [(arg 1, arg 2), (arg 0, arg 2)])
  | .mload | .mstore => plain (3 + expand [(arg 0, 32)])
  | .mstore8 => plain (3 + expand [(arg 0, 1)])
  | .sload =>
    let (cold, w) := slot (arg 0)
    let n := if cold > 0 then cold else 100
    ⟨n, n, w⟩
  | .sstore =>
    let (cold, w) := slot (arg 0)
    let n := cold + sstoreCost (g.original (arg 0)) (Storage.read g.original f.storage (arg 0)) (arg 1)
    -- EIP-2200: `SSTORE` fails unless more than 2300 gas is left
    ⟨if g.cancun then max n 2301 else n, n, w⟩
  | .tload | .tstore => plain 100
  | .jump => plain 8
  | .jumpi => plain 10
  | .log n => plain (375 + 375 * n + 8 * arg 1 + expand [(arg 0, arg 1)])
  | .call =>
    let to := arg 1 % U160
    let value := arg 2
    let (access, w) := account to
    -- a new account costs 25000, unless an earlier call of this execution created it
    let funded := f.calls.any fun r => r.to == to && r.value > 0 && r.success
    let required := access + expand [(arg 3, arg 4), (arg 5, arg 6)]
      + (if value > 0 then 9000 else 0)
      + (if value > 0 && g.dead to && !funded then 25000 else 0)
    -- the callee's 2300 stipend may come back unused
    ⟨required, required - (if value > 0 then 2300 else 0), w⟩
  | .staticcall =>
    let (access, w) := account (arg 1)
    let n := access + expand [(arg 2, arg 3), (arg 4, arg 5)]
    ⟨n, n, w⟩
  | .callcode | .delegatecall | .create | .create2 | .selfdestruct => plain 0

/-- A lower bound on the intrinsic gas of a transaction calling a contract with `data`
    (EIP-2028 calldata costs; access-list entries cost 2400 per address, 1900 per key). -/
def intrinsicGas (data : Bytes) (accessAddrs accessKeys : Nat) : Nat :=
  21000 + data.foldl (fun acc b => acc + if b == 0 then 4 else 16) 0
    + 2400 * accessAddrs + 1900 * accessKeys

end Conformance
