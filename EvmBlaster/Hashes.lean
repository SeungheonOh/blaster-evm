import EvmBlaster.Machine

/-!
# Collision freedom of the hashes an execution computes

keccak256 has collisions (more than `2^256` inputs, `2^256` outputs), so assuming that the
world's keccak256 is injective on *all* inputs while its answers are words
(`World.WF`) is contradictory: a theorem under both assumptions is vacuous. What is true of
real executions, with overwhelming probability, is that the hashes *they compute* do not
collide. `hashesOf` lists them (by running the machine, as `execute` does), and
`CollisionFree` states that a finite list of hash inputs has pairwise distinct hashes
(and, for structs stored at hashes, hashes at least `gap` apart). This assumption is
consistent, and quantifier-free once the list is known, so the solver can still find
counterexamples under it.
-/

namespace Evm

/-- A keccak256 input: length in bytes and 32-byte chunks. -/
abbrev HashInput := Nat × List Nat

/-- The input of the `KECCAK256` about to execute in frame `f`, if any. -/
def hashInput (c : Contract) (env : Env) (world : Query → Nat) (f : Frame) (acc : List HashInput) :
    List HashInput :=
  match c.code.fetch f.pc, f.stack with
  | some .keccak256, off :: len :: _ =>
    (len, Memory.chunks (memCtx c env world) f.memory ((len + 31) / 32) off len) :: acc
  | _, _ => acc

/-- The keccak256 inputs of the steps of `s`, in reverse order, after `acc`. -/
def hashesRun (s : State) (n : Nat) (acc : List HashInput) : List HashInput :=
  match n, s with
  | _, .halted _ => acc
  | 0, .running .. => acc
  | n + 1, .running c env world f => hashesRun (step c env world f) n (hashInput c env world f acc)

/-- The keccak256 inputs of a message call (as executed by `execute c env world fuel`). -/
def hashesOf (c : Contract) (env : Env) (world : Query → Nat) (fuel : Nat) : List HashInput :=
  hashesRun (.running c env world (Frame.init env)) fuel []

/-- `h` is distinct from (at least `gap` away from) the hash of every input of `hs` but
    `i` itself. -/
def apartFrom (world : Query → Nat) (gap : Nat) (i : HashInput) : List HashInput → Prop
  | [] => True
  | j :: js =>
    (i = j ∨ world (.keccak i.1 i.2) + gap ≤ world (.keccak j.1 j.2) ∨
      world (.keccak j.1 j.2) + gap ≤ world (.keccak i.1 i.2)) ∧ apartFrom world gap i js

/-- The hashes of the inputs `hs` are pairwise distinct (`gap = 1`), or at least `gap` apart
    (the slots of a struct stored at a hash), and at most `2^256 - gap`. -/
def CollisionFree (world : Query → Nat) (gap : Nat) : List HashInput → Prop
  | [] => True
  | i :: is => world (.keccak i.1 i.2) + gap ≤ U256 ∧ apartFrom world gap i is ∧
      CollisionFree world gap is

/-- The keccak256 input locating `m[k]` for a mapping `m` at slot `p`. -/
def mapKey (p k : Nat) : HashInput := (64, [k, p])

/-- The keccak256 inputs locating `m[k1][k2]` for a nested mapping `m` at slot `p`. -/
def mapKey2 (world : Query → Nat) (p k1 k2 : Nat) : List HashInput :=
  [(64, [k1, p]), (64, [k2, world (.keccak 64 [k1, p])])]

/-- The hashes a call computes, and the hashes `extra` a statement about it reads, do not
    collide (and are at least `gap` apart). The hypothesis to use instead of a global
    injectivity of keccak256, which `World.WF` contradicts. -/
def HashesFree (c : Contract) (env : Env) (world : Query → Nat) (fuel gap : Nat)
    (extra : List HashInput) : Prop :=
  CollisionFree world gap (extra ++ hashesOf c env world fuel)

end Evm
