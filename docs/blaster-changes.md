# Changes to Blaster

Blaster is vendored in [`vendor/Lean-blaster`](../vendor) (the exact upstream revision and
a detailed description of every change are in
[`vendor/UPSTREAMS.md`](../vendor/UPSTREAMS.md); the full diff is
`vendor/Lean-blaster.patch`). All changes are general-purpose, not EVM-specific: rewrite
rules for `Nat`, and one fix to the optimizer.

1. **Bitwise operators.** Upstream unfolds `&&&`, `|||`, `^^^` into well-founded recursion
   it cannot translate. They are now opaque. A small bit-support analysis (which bit
   positions a term may set, from literals, `% 2^k`, `/ 2^k`, `* 2^k`, disjoint sums and
   bound hypotheses) drives the rewrites: `x &&& N` for a literal mask becomes a sum of
   bit-range extracts (one per run of ones in `N`), and `|||`/`^^^` of operands with
   disjoint bits become `+`. Whatever remains gets exact recursive SMT definitions.
2. **Bit fields.** With the same analysis, `% 2^k` drops the addends of a sum that are
   multiples of `2^k`, `/ 2^k` divides them separately, and both vanish on terms below
   `2^k`. Writing a packed storage field and reading it (or its neighbours) back then
   simplifies to the expected values before the solver is called. These rules build their
   results directly instead of asking the optimizer for a restart: a restart inside an
   `if-then-else` branch can re-run the rule on the original branch forever.
3. **Merging bit fields**: adjacent fields of the same value in a sum,
   `((x / 2^p) % 2^w) * 2^q + ((x / 2^(p+w)) % 2^v) * 2^(q+w)`, become one field, so a
   word read byte by byte from memory collapses back into (a slice of) the stored word.
4. **`x % n = x` under a hypothesis `x < n`**, e.g. an address masked to 160 bits.
5. **An occurs check** (a fix, not a rule): a hypothesis `x = t` is no longer used to
   rewrite `x` when `t` contains `x`, which made the optimizer loop. Solidity's ABI check
   of a `bytes4` argument produces exactly such a hypothesis, `x = 2^224 * (x / 2^224)`,
   so every `supportsInterface` ran out of memory.

They come with tests in `vendor/Lean-blaster/Tests/Smt/SmtNat/SmtNatBitwise.lean`,
including false near-miss statements the rewrites must not prove and a regression test for
the occurs check. Their effect on this project: the packed-storage suite went from not
finishing in 20 minutes to 2 seconds.

After changing the vendored sources, rebuild the plugin with `lake build Blaster:shared`
(`lake build Blaster` alone does not rebuild it; `scripts/check-all.sh` does).
