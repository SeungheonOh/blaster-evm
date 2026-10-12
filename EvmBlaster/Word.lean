/-!
# 256-bit EVM words

Words are natural numbers below `2^256`, typed as plain `Nat` (Blaster does not resolve
type abbreviations in every position of its SMT translation). Every operation below returns
a word when its operands are words, so the invariant is kept by construction; the inputs of
an execution (calldata, storage, world answers, ...) are assumed to be words (`Env.WF`,
`World.WF`).

`Nat` is used instead of `BitVec 256` because Blaster reasons natively about `Nat`
(translated to SMT integers). Arithmetic by constants (masks, shifts, selectors) stays
linear. Bitwise `and`/`or`/`xor` use `Nat.land`/`Nat.lor`/`Nat.xor`, which the vendored
Blaster rewrites to arithmetic whenever the bit layout is syntactically known (masking,
packing) and otherwise translates to an exact recursive SMT definition.
-/

namespace Evm

/-- The number of 256-bit words, `2^256`. -/
def U256 : Nat := 2 ^ 256

/-- The number of 160-bit addresses, `2^160`. -/
def U160 : Nat := 2 ^ 160


/-- A value boxed in a constructor.

Blaster unrolls a recursive call only when every explicit argument is a constructor
application; otherwise the function is sent to the SMT solver as a recursive definition.
A constructor of an `inductive` type may contain free variables, but a `structure`
constructor counts only when all of its fields are constructors themselves. The recursive
helpers of the machine recurse on concrete data (code, memory and storage write lists,
stacks) and also carry arguments that may be symbolic (a storage key, a memory offset):
those are boxed in this single-constructor *inductive* (deliberately not a `structure`)
so that symbolic execution unrolls the recursion. -/
inductive Box (α : Type) where
  | mk (val : α)

namespace Word

def add (a b : Nat) : Nat := (a + b) % U256
def mul (a b : Nat) : Nat := (a * b) % U256
def sub (a b : Nat) : Nat := (a + (U256 - b)) % U256
-- `Nat.div` already returns `0` on a zero divisor.
def div (a b : Nat) : Nat := a / b
def mod (a b : Nat) : Nat := if b = 0 then 0 else a % b
def addmod (a b n : Nat) : Nat := if n = 0 then 0 else (a + b) % n
def mulmod (a b n : Nat) : Nat := if n = 0 then 0 else (a * b) % n
/-- `a ^ b mod 2^256` by square-and-multiply (`b < 2^256` takes at most 256 rounds). -/
def powMod (a b : Nat) : Nat := go 256 (a % U256) b 1
 where
  go : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, e, acc =>
    if e = 0 then acc
    else go fuel (base * base % U256) (e / 2) (if e % 2 = 1 then acc * base % U256 else acc)

/-- `EXP`. Small exponents (the common case: masks, `256 ** k`) use `^` directly; large
    ones would make `a ^ b` astronomically large, so they go through `powMod`. -/
def exp (a b : Nat) : Nat := if b < 256 then (a ^ b) % U256 else powMod a b

/-- Two's complement reading of a word. -/
def toInt (a : Nat) : Int := if a < 2 ^ 255 then Int.ofNat a else Int.ofNat a - Int.ofNat U256

/-- The word representing an integer modulo `2^256`. -/
def ofInt (i : Int) : Nat := Int.toNat (i % Int.ofNat U256)

def sdiv (a b : Nat) : Nat := if b = 0 then 0 else ofInt (Int.tdiv (toInt a) (toInt b))
def smod (a b : Nat) : Nat := if b = 0 then 0 else ofInt (Int.tmod (toInt a) (toInt b))

def signextend (b x : Nat) : Nat :=
  if b < 31 then
    let bits := 8 * (b + 1)
    let low := x % 2 ^ bits
    if low < 2 ^ (bits - 1) then low else low + (U256 - 2 ^ bits)
  else x

def bool (c : Prop) [Decidable c] : Nat := if c then 1 else 0

def lt (a b : Nat) : Nat := bool (a < b)
def gt (a b : Nat) : Nat := bool (b < a)
def slt (a b : Nat) : Nat := bool (toInt a < toInt b)
def sgt (a b : Nat) : Nat := bool (toInt b < toInt a)
def eq (a b : Nat) : Nat := bool (a = b)
def iszero (a : Nat) : Nat := bool (a = 0)

def and (a b : Nat) : Nat := a &&& b
def or (a b : Nat) : Nat := a ||| b
def xor (a b : Nat) : Nat := a ^^^ b
def not (a : Nat) : Nat := U256 - 1 - a

/-- `BYTE i x`: the `i`-th most significant byte of `x`. -/
def byte (i x : Nat) : Nat := if i < 32 then (x / 2 ^ (8 * (31 - i))) % 256 else 0
def shl (s x : Nat) : Nat := if s < 256 then (x * 2 ^ s) % U256 else 0
def shr (s x : Nat) : Nat := if s < 256 then x / 2 ^ s else 0
def sar (s x : Nat) : Nat :=
  if s < 256 then ofInt (toInt x / Int.ofNat (2 ^ s))
  else if x < 2 ^ 255 then 0 else U256 - 1

/-- The first `n` bytes of `w` (the rest zeroed), i.e. `w` truncated to an `n`-byte
    big-endian prefix. Used to pad partial words. -/
def keepBytes (n : Nat) (w : Nat) : Nat :=
  if n < 32 then (w / 2 ^ (8 * (32 - n))) * 2 ^ (8 * (32 - n)) else w

/-- Big-endian assembly of the 32 bytes `f a, f (a+1), ..., f (a+31)` into a word.
    Written out rather than recursive: Blaster unrolls a recursive function only when all
    its explicit arguments are constructors, which a symbolic accumulator is not. -/
def assemble (f : Nat → Nat) (a : Nat) : Nat :=
  f (a + 0) * 2 ^ 248
  + f (a + 1) * 2 ^ 240
  + f (a + 2) * 2 ^ 232
  + f (a + 3) * 2 ^ 224
  + f (a + 4) * 2 ^ 216
  + f (a + 5) * 2 ^ 208
  + f (a + 6) * 2 ^ 200
  + f (a + 7) * 2 ^ 192
  + f (a + 8) * 2 ^ 184
  + f (a + 9) * 2 ^ 176
  + f (a + 10) * 2 ^ 168
  + f (a + 11) * 2 ^ 160
  + f (a + 12) * 2 ^ 152
  + f (a + 13) * 2 ^ 144
  + f (a + 14) * 2 ^ 136
  + f (a + 15) * 2 ^ 128
  + f (a + 16) * 2 ^ 120
  + f (a + 17) * 2 ^ 112
  + f (a + 18) * 2 ^ 104
  + f (a + 19) * 2 ^ 96
  + f (a + 20) * 2 ^ 88
  + f (a + 21) * 2 ^ 80
  + f (a + 22) * 2 ^ 72
  + f (a + 23) * 2 ^ 64
  + f (a + 24) * 2 ^ 56
  + f (a + 25) * 2 ^ 48
  + f (a + 26) * 2 ^ 40
  + f (a + 27) * 2 ^ 32
  + f (a + 28) * 2 ^ 24
  + f (a + 29) * 2 ^ 16
  + f (a + 30) * 2 ^ 8
  + f (a + 31) * 2 ^ 0

/-- Byte `i` (big-endian, `i < 32`) of word `w`. -/
def byteOf (w : Nat) (i : Nat) : Nat := (w / 2 ^ (8 * (31 - i))) % 256

end Word

end Evm
