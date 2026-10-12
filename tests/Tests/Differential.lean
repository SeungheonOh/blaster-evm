import Tests.Differential.Cases

/-!
# Differential suite: the formal machine against geth

Each case of `Cases.lean` is an artificial program whose outcome was recorded from
go-ethereum's reference interpreter (see `tests/difftest/gen_cases.py`). The machine must
produce the same returned/reverted bytes and the same final storage, and halt exceptionally
exactly when geth does. Programs avoid what the model deliberately abstracts (gas, contract
creation, precompiles).
-/

namespace Tests.Differential
open Evm Tests

def Expected.matches : Expected → Outcome → Bool
  | .success ret st, .success r s => toHex r == ret && s == st
  | .revert ret, .revert r => toHex r == ret
  | .exception _, .exception => true
  | _, _ => false

def describe : Outcome → String
  | .success r s => s!"success {toHex r} storage {s}"
  | .revert r => s!"revert {toHex r}"
  | .exception => "exception"
  | .unsupported => "unsupported"
  | .outOfFuel => "out of fuel"

/-- The cases where the machine disagrees with geth. -/
def failures : List String :=
  cases.filterMap fun c =>
    let o := runHex c.code c.input
    if c.expected.matches o then none else some s!"{c.name}: {describe o}"

#guard cases.length = 226
#guard failures = []

end Tests.Differential
