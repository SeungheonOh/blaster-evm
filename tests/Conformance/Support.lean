import Lean.Data.Json
import Std.Data.HashMap
import EvmBlaster.Machine
import Tests.Support.Keccak

/-!
# Conformance: fixtures and Ethereum encodings

Reading the JSON fixtures of the Ethereum test suites (hex numbers, byte strings,
accounts), and the encodings the expected results are stated in: RLP and the hash of an
execution's logs (legacy VM tests), and the 2048-bit logs bloom (blockchain tests).
-/

namespace Conformance
open Lean Evm

abbrev Bytes := Array UInt8

/-! ### Fixture fields -/

/-- A hex number `0x…` (`0x` alone is zero). -/
def hexNat (s : String) : Except String Nat := do
  let digits := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  digits.toList.foldlM (init := 0) fun acc ch => do
    let d ←
      if '0' ≤ ch ∧ ch ≤ '9' then pure (ch.toNat - '0'.toNat)
      else if 'a' ≤ ch ∧ ch ≤ 'f' then pure (ch.toNat - 'a'.toNat + 10)
      else if 'A' ≤ ch ∧ ch ≤ 'F' then pure (ch.toNat - 'A'.toNat + 10)
      else throw s!"invalid hex number {s}"
    pure (acc * 16 + d)

def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{k}'"

def hasField (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

def str (j : Json) (k : String) : Except String String := do (← field j k).getStr?

def num (j : Json) (k : String) : Except String Nat := do hexNat (← str j k)

/-- A hex number field, `d` when absent. -/
def numD (j : Json) (k : String) (d : Nat) : Except String Nat :=
  if hasField j k then num j k else pure d

def bytes (j : Json) (k : String) : Except String Bytes := do parseHex (← str j k)

/-- The members of a JSON object, in key order. -/
def members (j : Json) : Except String (List (String × Json)) := do
  return (← j.getObj?).toList

/-! ### Accounts -/

structure Account where
  balance : Nat
  nonce : Nat
  code : Bytes
  storage : Std.HashMap Nat Nat

abbrev Accounts := Std.HashMap Nat Account

def parseStorage (j : Json) : Except String (Std.HashMap Nat Nat) := do
  (← members j).foldlM (init := {}) fun m (k, v) => do
    return m.insert (← hexNat k) (← hexNat (← v.getStr?))

def parseAccount (j : Json) : Except String Account := do
  return { balance := ← num j "balance", nonce := ← num j "nonce", code := ← bytes j "code"
           storage := ← parseStorage (← field j "storage") }

def parseAccounts (j : Json) : Except String Accounts := do
  (← members j).foldlM (init := {}) fun m (a, acct) => do
    return m.insert (← hexNat a) (← parseAccount acct)

/-- The nonzero slots of a storage, sorted by key. -/
def storageList (m : Std.HashMap Nat Nat) : List (Nat × Nat) :=
  (m.toList.filter (·.2 != 0)).mergeSort (fun a b => a.1 ≤ b.1)

/-- EIP-161: an account that does not exist or has no code, nonce or balance. -/
def isDead (accts : Accounts) (a : Nat) : Bool :=
  match accts.get? a with
  | none => true
  | some acct => acct.balance == 0 && acct.nonce == 0 && acct.code.isEmpty

/-- `EXTCODEHASH` of `a`: zero for dead accounts, otherwise the hash of the code. -/
def codeHash (accts : Accounts) (a : Nat) : Nat :=
  if isDead accts a then 0
  else Tests.Keccak.keccak256 ((accts.get? a).map (·.code) |>.getD #[])

/-! ### Results as bytes -/

/-- Big-endian bytes of `n`, exactly `w` of them. -/
def wordBytes (n w : Nat) : List UInt8 :=
  (List.range w).map fun i => UInt8.ofNat ((n / 2 ^ (8 * (w - 1 - i))) % 256)

/-- Minimal big-endian bytes of `n` (none for zero). -/
def minBytes (n : Nat) : List UInt8 :=
  if n == 0 then [] else wordBytes n ((Nat.log2 n) / 8 + 1)

/-- The bytes of a memory slice. -/
def sliceBytes (cx : MemCtx) (s : Slice) : Bytes :=
  (Array.range s.len).map fun i => UInt8.ofNat (Memory.byteAt cx s.mem (s.off + i))

/-- A log as Ethereum stores it: emitter, topics, data. -/
structure Log where
  address : Nat
  topics : List Nat
  data : Bytes

/-- The logs of a frame, oldest first. -/
def frameLogs (cx : MemCtx) (address : Nat) (f : Frame) : List Log :=
  f.logs.reverse.map fun l => ⟨address, l.topics, sliceBytes cx l.data⟩

/-! ### RLP, logs hash, logs bloom -/

inductive Rlp where
  | bytes (b : List UInt8)
  | list (items : List Rlp)

/-- The RLP length prefix of a payload of `len` bytes (`base` is `0x80` or `0xc0`). -/
def rlpPrefix (base len : Nat) : List UInt8 :=
  if len ≤ 55 then [UInt8.ofNat (base + len)]
  else let l := minBytes len; UInt8.ofNat (base + 55 + l.length) :: l

partial def Rlp.encode : Rlp → List UInt8
  | .bytes [b] => if b < 0x80 then [b] else [0x81, b]
  | .bytes b => rlpPrefix 0x80 b.length ++ b
  | .list items =>
    let payload := (items.map Rlp.encode).flatten
    rlpPrefix 0xc0 payload.length ++ payload

/-- keccak256 of the RLP list of logs (the `logs` field of the VM tests). -/
def logsHash (logs : List Log) : Nat :=
  let item (l : Log) : Rlp :=
    .list [.bytes (wordBytes l.address 20), .list (l.topics.map fun t => .bytes (wordBytes t 32)),
           .bytes l.data.toList]
  Tests.Keccak.keccak256 (Rlp.encode (.list (logs.map item))).toArray

/-- The logs bloom of the yellow paper, as a 2048-bit number (the header field read as a
    big-endian number): for the emitter and each topic, three bits chosen by its hash. -/
def logsBloom (logs : List Log) : Nat :=
  let add (bloom : Nat) (b : List UInt8) : Nat :=
    let h := Tests.Keccak.keccak256 b.toArray
    let byte (i : Nat) := (h / 2 ^ (8 * (31 - i))) % 256
    [0, 2, 4].foldl (fun acc i => acc ||| 2 ^ ((byte i * 256 + byte (i + 1)) % 2048)) bloom
  logs.foldl (fun bloom l =>
    l.topics.foldl (fun acc t => add acc (wordBytes t 32)) (add bloom (wordBytes l.address 20))) 0

-- The RLP of an empty list hashes to the `logs` value of tests without logs.
#guard Tests.Keccak.keccak256 (Rlp.encode (.list [])).toArray =
  0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
#guard Rlp.encode (.bytes []) = [0x80]
#guard Rlp.encode (.bytes [0x7f]) = [0x7f]
#guard Rlp.encode (.bytes (List.replicate 56 1)) = [0xb8, 56] ++ List.replicate 56 1

end Conformance
