import Lean.Data.Json
import EvmBlaster.Spec

/-!
# Replaying a counterexample

The annotation toolchain (`blaster-evm`) replays every counterexample Blaster finds: it
runs the machine's own `step` on the counterexample's environment and chain state and
reports what happened, as JSON, so that the counterexample can be shown in Solidity terms
(the function called, the outcome, the storage changes, the Ether sent, the events). The
replay also records the keccak256 queries of the execution, to check whether the
counterexample relies on a hash collision.
-/

namespace Evm.Replay
open Lean

deriving instance DecidableEq for Query

def bytesHex (bs : List Nat) : String :=
  "0x" ++ String.join (bs.map fun b =>
    let d := Nat.toDigits 16 b
    String.mk (if d.length < 2 then '0' :: d else d))

def sliceBytes (cx : MemCtx) (s : Slice) : List Nat :=
  (List.range s.len).map fun i => Memory.byteAt cx s.mem (s.off + i)

/-- What the replay records along the execution. -/
structure Trace where
  keccaks : Array Json := #[]
  sloads : Array Json := #[]
  steps : Nat := 0

/-- Hashes of more bytes than this are not recorded (a huge length is out of gas anyway). -/
def maxHashLen : Nat := 1 <<< 20

partial def drive (c : Contract) (env : Env) (world : Query → Nat) (fuel : Nat) (f : Frame)
    (t : Trace) : Result × Frame × Trace :=
  if fuel = 0 then (.outOfFuel, f, t) else
  let cx := memCtx c env world
  let t := match c.code.fetch f.pc, f.stack with
    | some .keccak256, off :: len :: _ =>
      if len ≤ maxHashLen then
        let ws := Memory.chunks cx f.memory ((len + 31) / 32) off len
        let entry := Json.mkObj
          [("len", toJson len), ("words", toJson ws), ("value", toJson (world (.keccak len ws)))]
        { t with keccaks := t.keccaks.push entry }
      else t
    | some .sload, k :: _ =>
      let entry := Json.mkObj
        [("key", toJson k), ("value", toJson (Storage.read (World.storage world) f.storage k)),
         ("before", toJson (World.storage world k))]
      { t with sloads := t.sloads.push entry }
    | _, _ => t
  let t := { t with steps := t.steps + 1 }
  match step c env world f with
  | .halted r => (r, f, t)
  | .running _ _ _ f' => drive c env world (fuel - 1) f' t

/-- Replay a call and describe it as JSON. -/
def run (c : Contract) (env : Env) (world : Query → Nat) (fuel : Nat) : String :=
  let (r, last, t) := drive c env world fuel (Frame.init env) {}
  let cx := memCtx c env world
  let instr := (c.code.fetch last.pc).map (fun i => toString (repr i)) |>.getD "end of code"
  let cd := env.msg.calldata
  let common : List (String × Json) :=
    [("steps", toJson t.steps), ("fuel", toJson fuel), ("keccak", Json.arr t.keccaks), ("sloads", Json.arr t.sloads),
     ("pc", toJson last.pc), ("instr", toJson instr),
     ("selector", toJson cd.selector), ("args", toJson cd.args), ("dataSize", toJson cd.size),
     ("caller", toJson env.msg.caller), ("value", toJson env.msg.callvalue),
     ("address", toJson env.msg.address), ("origin", toJson env.tx.origin),
     ("timestamp", toJson env.block.timestamp), ("number", toJson env.block.number),
     ("balanceBefore", toJson env.balance)]
  let fields : List (String × Json) := match r with
    | .success f out =>
      let keys := (f.storage.map (·.1)).eraseDups
      [("result", "success"), ("output", toJson (bytesHex (sliceBytes cx out))),
       ("storage", Json.arr (keys.toArray.map fun k => Json.mkObj
          [("key", toJson k), ("before", toJson (World.storage world k)),
           ("after", toJson (f.sload world k))])),
       ("balance", toJson f.balance),
       ("calls", Json.arr (f.calls.reverse.toArray.map fun cr => Json.mkObj
          [("kind", toJson (match cr.kind with | .call => "call" | .staticcall => "staticcall")),
           ("to", toJson cr.to), ("value", toJson cr.value), ("success", toJson cr.success),
           ("input", toJson (bytesHex (sliceBytes cx cr.input)))])),
       ("logs", Json.arr (f.logs.reverse.toArray.map fun l => Json.mkObj
          [("topics", toJson l.topics), ("data", toJson (bytesHex (sliceBytes cx l.data)))]))]
    | .revert out => [("result", "revert"), ("output", toJson (bytesHex (sliceBytes cx out)))]
    | .exception => [("result", "exception")]
    | .unsupported i => [("result", "unsupported"), ("unsupported", toJson (toString (repr i)))]
    | .outOfFuel => [("result", "outOfFuel")]
  (Json.mkObj (fields ++ common)).compress

/-- An environment as JSON (for counterexamples that mention it outside a call). -/
def envJson (env : Env) : String :=
  (Json.mkObj [("caller", toJson env.msg.caller), ("value", toJson env.msg.callvalue),
    ("address", toJson env.msg.address), ("origin", toJson env.tx.origin),
    ("timestamp", toJson env.block.timestamp), ("number", toJson env.block.number),
    ("coinbase", toJson env.block.coinbase), ("balance", toJson env.balance),
    ("selector", toJson env.msg.calldata.selector), ("args", toJson env.msg.calldata.args),
    ("dataSize", toJson env.msg.calldata.size)]).compress

end Evm.Replay
