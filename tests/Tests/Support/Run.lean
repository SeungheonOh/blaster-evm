import EvmBlaster
import Tests.Support.Keccak

/-!
# Concrete runs of artificial programs

The world and environment of `geth evm run` (go-ethereum's reference interpreter, used to
produce the expected outcomes of the differential suite): a fresh chain with empty storage
and accounts, a real keccak256, and calls to (empty) accounts that succeed without return
data.
-/

namespace Tests
open Evm

/-- A fresh chain with the given initial storage for the executing contract. -/
def freshWorld (storage : Nat → Nat := fun _ => 0) : Query → Nat
  | .storage k => storage k
  | .keccak n ws => Keccak.keccak256 (Keccak.bytesOfChunks n ws)
  | .callSuccess _ => 1
  | _ => 0

/-- `geth evm run`'s default context: receiver `"receiver"`, sender `"sender"`. -/
def gethEnv (input : Array UInt8) (callvalue balance : Nat := 0) : Env :=
  { block := { coinbase := 0, timestamp := 0, number := 0, prevrandao := 0,
               gaslimit := 10000000000, chainid := 1337, basefee := 1000000000,
               blobbasefee := 0 }
    tx := { origin := 0x73656e646572, gasprice := 0 }
    msg := { address := 0x7265636569766572, caller := 0x73656e646572, callvalue := callvalue,
             calldata := Calldata.ofBytes input }
    balance := balance }

/-- What a run produced, in a form comparable with geth's output. -/
inductive Outcome where
  /-- Returned bytes and the nonzero storage slots afterwards (sorted by key). -/
  | success (ret : List Nat) (storage : List (Nat × Nat))
  | revert (ret : List Nat)
  | exception
  | unsupported
  | outOfFuel
deriving Repr, DecidableEq, Inhabited

def sliceBytes (cx : MemCtx) (s : Slice) : List Nat :=
  (List.range s.len).map fun i => Memory.byteAt cx s.mem (s.off + i)

/-- Final values of the written slots that are nonzero, sorted by key. -/
def finalStorage (world : Query → Nat) (f : Frame) : List (Nat × Nat) :=
  let keys := (f.storage.map (·.1)).eraseDups
  let kvs := keys.map fun k => (k, f.sload world k)
  (kvs.filter (·.2 != 0)).mergeSort (fun a b => a.1 ≤ b.1)

def outcomeOf (c : Contract) (env : Env) (world : Query → Nat) (fuel : Nat) : Outcome :=
  let cx := memCtx c env world
  match execute c env world fuel with
  | .success f out => .success (sliceBytes cx out) (finalStorage world f)
  | .revert out => .revert (sliceBytes cx out)
  | .exception => .exception
  | .unsupported _ => .unsupported
  | .outOfFuel => .outOfFuel

def hexBytes (s : String) : Array UInt8 :=
  match parseHex s with
  | .ok b => b
  | .error _ => #[]

/-- Run hex-encoded `code` on hex-encoded `input` in geth's default context. -/
def runHex (code input : String) (storage : Nat → Nat := fun _ => 0) (fuel := 200000) : Outcome :=
  outcomeOf (Contract.ofBytes (hexBytes code)) (gethEnv (hexBytes input)) (freshWorld storage) fuel

def toHex (bs : List Nat) : String :=
  "0x" ++ String.join (bs.map fun b =>
    let d := Nat.toDigits 16 b
    String.mk (if d.length < 2 then '0' :: d else d))

end Tests
