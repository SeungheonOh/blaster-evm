import Lean
import EvmBlaster

/-!
# The EVM ledger API for UAL annotations

What UAL `PREDICATE` and `PROPERTY` annotations on Solidity contracts are written against,
in the role `CardanoLedgerApi` plays for Cardano contracts: the chain state, snapshots of a
contract's storage before and after a call, the outcome of a call, and the assumptions the
EVM model makes.

An `ONCHAIN` function `f` of contract `C` becomes `C.f (args…) (env : Env) (world : World) :
Result`: a message call to the contract's runtime bytecode with the ABI-encoded arguments,
in environment `env` (caller, value, block) and chain state `world`.
-/

namespace UAL
open Lean Evm

/-- The chain state: the answer to every query an execution can make (storage, keccak256,
    other accounts, outcomes of calls). (A macro rather than an abbreviation: Blaster needs
    the function type written out.) -/
macro "World" : term => `(Evm.Query → Nat)

/-- A view of a contract's storage: its slots, and the keccak256 used to locate mapping
    entries. -/
structure Snapshot where
  world : Query → Nat
  storage : Nat → Nat

/-- The contract's storage before the call. -/
def before (world : World) : Snapshot := ⟨world, World.storage world⟩

/-- The contract's storage after the call `r`: the final storage if it succeeded,
    unchanged otherwise (a revert discards every write). -/
def after (world : World) (r : Result) : Snapshot :=
  ⟨world, fun k => match r with
    | .success f _ => f.sload world k
    | _ => World.storage world k⟩

/-- The call succeeded (`STOP` or `RETURN`). -/
def isSuccessful (r : Result) : Prop := r.isSuccess

/-- The call failed (`REVERT` or an exceptional halt): it had no effect. -/
def isReverted (r : Result) : Prop := r.isFailure

/-- The execution stays within the modelled fragment of the EVM and the step budget. Every
    property checks it for the calls it mentions (see `#ual_property`). -/
def covered (r : Result) : Prop :=
  match r with
  | .unsupported _ | .outOfFuel => False
  | _ => True

/-- The contract's Ether balance after the call (before it: `env.balance`). -/
def balanceAfter (env : Env) (r : Result) : Nat :=
  match r with
  | .success f _ => f.balance
  | _ => env.balance

/-- Ether sent to `a` by the call (through its successful outgoing calls). -/
def paidTo (a : Nat) (r : Result) : Nat :=
  match r with
  | .success f _ => Sol.paidTo a f.calls
  | _ => 0

/-- Ether sent by the call. -/
def sent (r : Result) : Nat :=
  match r with
  | .success f _ => Sol.sentBy f.calls
  | _ => 0

/-- An event signature (its first topic). -/
structure Event where
  topic : Nat

/-- The call emitted event `e`. -/
def emits (e : Event) (r : Result) : Prop :=
  match r with
  | .success f _ => Sol.emittedIn e.topic f.logs = true
  | _ => False

/-! Decidability, to evaluate the parts of a statement on a counterexample. -/

instance (r : Result) : Decidable (isSuccessful r) := by
  unfold isSuccessful Result.isSuccess; split <;> infer_instance
instance (r : Result) : Decidable (isReverted r) := by
  unfold isReverted Result.isFailure; split <;> infer_instance
instance (r : Result) : Decidable (covered r) := by
  unfold covered; split <;> infer_instance
instance (e : Event) (r : Result) : Decidable (emits e r) := by
  unfold emits; split <;> infer_instance

/-! ### The call environment, Solidity names -/

def _root_.Evm.Env.sender (e : Env) : Nat := e.msg.caller
def _root_.Evm.Env.value (e : Env) : Nat := e.msg.callvalue
def _root_.Evm.Env.origin (e : Env) : Nat := e.tx.origin
def _root_.Evm.Env.timestamp (e : Env) : Nat := e.block.timestamp
def _root_.Evm.Env.number (e : Env) : Nat := e.block.number
def _root_.Evm.Env.coinbase (e : Env) : Nat := e.block.coinbase
def _root_.Evm.Env.self (e : Env) : Nat := e.msg.address

/-! ### Assumptions

keccak256 collision freedom is assumed only for the hashes a property involves (see
`Evm.CollisionFree`): assuming it for all inputs would contradict the 256-bit range of
hashes, and make every theorem vacuous. -/

/-- What the front end knows about a contract's storage. -/
structure ContractInfo where
  /-- The storage slots of the plain state variables. -/
  slots : Nat
  /-- The largest struct stored in a mapping, in slots (`0`: none). -/
  structSize : Nat
  /-- The slots of `string`/`bytes` state variables. -/
  stringSlots : List Nat
  /-- Whether the code hashes at all (otherwise collision resistance is irrelevant). -/
  usesKeccak : Bool
deriving Inhabited

/-- Every `string`/`bytes` state variable holds a short value (under 32 bytes). -/
def ShortStrings (world : World) : List Nat → Prop
  | [] => True
  | k :: ks => Sol.ShortString (World.storage world k) ∧ ShortStrings world ks

/-- The assumptions of the EVM model about a chain state: its values are words, hashes do
    not land on the plain state variables' slots, strings are short. -/
def ValidWorld (info : ContractInfo) (world : World) : Prop :=
  World.WF world ∧ World.KeccakAbove world info.slots ∧ ShortStrings world info.stringSlots

/-! ### `ONCHAIN` functions -/

/-- Marks the Lean functions generated for `ONCHAIN` Solidity functions. Each such `f` comes
    with `f.inputs` (its arguments are valid values of their Solidity types), `f.hashes` (the
    keccak256 inputs of the call) and `f.trace` (which replays the call and describes it as
    JSON, `Evm.Replay.run`). -/
initialize onchainAttr : TagAttribute ←
  registerTagAttribute `ual_onchain "a UAL ONCHAIN function (a message call to a contract)"

/-- Marks the generated storage accessors that read mapping entries; each `x` comes with
    `x.hashes`, the keccak256 inputs locating the entry. -/
initialize storageAttr : TagAttribute ←
  registerTagAttribute `ual_storage "a storage accessor reading hashed slots"

end UAL
