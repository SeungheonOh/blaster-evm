/-!
# Keccak-256

A plain executable Keccak-256 (the original Keccak padding used by Ethereum, not SHA3-256),
used by the test suites to answer `Query.keccak` exactly as a real EVM would. The proofs
never use it: there, keccak256 stays uninterpreted.
-/

namespace Tests.Keccak

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets, indexed by `x + 5 * y`. -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
  41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

def rotl (v n : UInt64) : UInt64 := if n == 0 then v else (v <<< n) ||| (v >>> (64 - n))

/-- One round of Keccak-f[1600] on the 25 lanes `a` (index `x + 5 * y`). -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ
  let c := (Array.range 5).map fun x => a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  let d := (Array.range 5).map fun x => c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
  let a := (Array.range 25).map fun i => a[i]! ^^^ d[i % 5]!
  -- ρ and π
  let mut b := Array.replicate 25 (0 : UInt64)
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! rotations[x + 5 * y]!)
  -- χ
  let a := (Array.range 25).map fun i =>
    let x := i % 5
    let y := i / 5
    b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  -- ι
  return a.set! 0 (a[0]! ^^^ rc)

def permute (a : Array UInt64) : Array UInt64 := roundConstants.foldl round a

/-- Keccak-256 of a byte string, as a big-endian 256-bit number. -/
def keccak256 (msg : Array UInt8) : Nat := Id.run do
  let rate := 136
  -- padding: 0x01, zeros, 0x80 in the last byte of the block
  let mut m := msg.push 0x01
  while m.size % rate != 0 do
    m := m.push 0
  m := m.set! (m.size - 1) (m[m.size - 1]! ||| 0x80)
  let mut st := Array.replicate 25 (0 : UInt64)
  for blk in [0:m.size / rate] do
    for i in [0:rate / 8] do
      let mut lane : UInt64 := 0
      for j in [0:8] do
        lane := lane ||| ((m[blk * rate + 8 * i + j]!).toUInt64 <<< (8 * j).toUInt64)
      st := st.set! i (st[i]! ^^^ lane)
    st := permute st
  -- squeeze 32 bytes: lanes 0..3, little-endian bytes, read big-endian
  let mut out : Nat := 0
  for i in [0:4] do
    for j in [0:8] do
      out := out * 256 + ((st[i]! >>> (8 * j).toUInt64) &&& 0xff).toNat
  return out

/-- The bytes of a `len`-byte string given as 32-byte big-endian chunks. -/
def bytesOfChunks (len : Nat) (chunks : List Nat) : Array UInt8 :=
  (Array.range len).map fun i => UInt8.ofNat ((chunks.getD (i / 32) 0 / 2 ^ (8 * (31 - i % 32))) % 256)

#guard keccak256 #[] = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
-- value computed by geth's KECCAK256 opcode
#guard keccak256 "abc".toUTF8.data = 0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

-- function selectors
#guard keccak256 "transfer(address,uint256)".toUTF8.data / 2 ^ 224 = 0xa9059cbb
#guard keccak256 "withdraw(uint256)".toUTF8.data / 2 ^ 224 = 0x2e1a7d4d

end Tests.Keccak
