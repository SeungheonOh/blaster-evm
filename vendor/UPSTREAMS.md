# Vendored upstream sources

| Directory | Upstream | Revision |
| --- | --- | --- |
| `Lean-blaster` | <https://github.com/input-output-hk/Lean-blaster>, branch `beta-lambda-cache-optimization` (the branch PlutusCoreBlaster uses) | `c0ef8c0ddef1666aa3d3c1e382ba6a90d0882d3a` |

The whole repository is vendored (minus `.git`), so its own test suite still runs
(`cd vendor/Lean-blaster && lake test`). `Lean-blaster.patch` is the complete diff of the
local changes against that revision.

## Local changes

1. **Bitwise operators on `Nat`** (`Nat.land`, `Nat.lor`, `Nat.xor`). Upstream unfolds
   them to `Nat.bitwise`, whose well-founded recursion the SMT translation cannot handle,
   so any goal mentioning `&&&`, `|||` or `^^^` was undetermined. They are now opaque, with
   - constant folding, identities (`x &&& 0 = 0`, `x ^^^ x = 0`, ...) and commutative
     normalisation (`Blaster/Optimize/Rewriting/OptimizeNat.lean`, `Utils.lean`);
   - a *bit-support* analysis (`natBitSupport`): from the shape of a term (literals,
     `% 2^k`, `/ 2^k`, `* 2^k`, sums of disjoint parts, bitwise operators,
     `if-then-else`) and from bounds `x < 2^k` among the hypotheses in scope, it computes
     intervals of bit positions that may be set;
   - mask rules: `x &&& N` with a literal `N` becomes the sum, over the runs `[lo, hi)` of
     one bits of `N` that meet the support of `x`, of `2^lo * ((x % 2^hi) / 2^lo)`; e.g.
     `x &&& (2^k - 1) = x % 2^k`, and `x &&& not(0xff << 160)` (two runs) keeps bits
     `[0, 160)` and `[168, 256)`;
   - disjoint-bits rules: when the supports of the operands are disjoint, `|||` and `^^^`
     become `+` and `&&&` becomes `0`. With the mask rules this is what makes Solidity's
     masked read-modify-write of packed storage slots tractable;
   - exact recursive SMT definitions for the applications that remain
     (`Blaster/Smt/Env.lean`, `Term.lean`, `Translate/Application.lean`).
2. **Bit-field rules for `%` and `/` by powers of two**, from the same analysis
   (`bitModReduce?`, `bitDivReduce?`): `e % 2^k = e` and `e / 2^k = 0` when `e < 2^k`;
   in a sum, addends that are multiples of `2^k` are dropped by `% 2^k` and divided
   separately (exactly) by `/ 2^k`. Reading a packed field back after writing it then
   simplifies to the written value before anything reaches the solver.
   Both rules return terms that need no further rewriting (each `/ 2^k` of an addend is
   simplified directly: literals, constant factors, nested sums) and never call
   `setRestart`. A restart requested inside an `if-then-else` or `match` branch can make
   the optimizer re-optimize the branch from its original body, where the rule fires
   again: an early version that restarted looped forever on the signed-arithmetic tests.
   The analysis is kept cheap on the large terms of long executions: it looks at most 6
   levels deep, and only looks up bounds of atoms (variables, projections, applications of
   a variable) among the hypotheses.
3. **Merging adjacent bit fields** (`mergeBitFields?`, applied to `Nat.add`): among the
   addends of a sum, `((x / 2^p) % 2^w) * 2^q + ((x / 2^(p+w)) % 2^v) * 2^(q+w)` becomes
   `((x / 2^p) % 2^(w+v)) * 2^q`. A word assembled byte by byte from a stored value (an
   unaligned memory read) collapses back into a single field of that value.
4. **`x % n` under a bound hypothesis**: `x % n` is rewritten to `x` when `x < n` is a
   hypothesis in scope (`modBoundedInHyps`). Typical case: an address `a < 2^160` masked to
   160 bits.
5. **Tests**: `Tests/Smt/SmtNat/SmtNatBitwise.lean` covers these changes, including false
   near-miss statements that the rewrites must not prove.

## Rebuilding the plugin

Examples and tests load Blaster's native library (`.lake/build/lib/libBlaster.so`).
`lake build` of a dependent module rebuilds it, but `lake build Blaster` alone does not:
after changing the vendored sources, run `lake build Blaster:shared` before using
`scripts/run-file.sh` (`scripts/check-all.sh` does it).
