# Findings: feasibility, limits, trust

- **It works on real bytecode.** Solidity's dispatcher, ABI decoding (including dynamic
  arrays), checked arithmetic, custom errors, revert strings, packed storage, mappings,
  structs in mappings, events and external calls all execute symbolically, as does
  OpenZeppelin code and 2017 mainnet bytecode. Typical properties over *all* calldata take
  1 to 30 seconds; properties quantifying over all holders of a mapping take minutes.
- **Word arithmetic as `Nat` is adequate** once bitwise operators are supported. Masks and
  shifts by constants stay linear; the remaining hard cases are byte-level reasoning
  (addressed by merging byte fields back into words) and quantifiers over mapping keys.
- **The chain-state oracle is the right interface.** Every assumption is visible in the
  theorem, and several examples show why they matter: without the keccak assumptions,
  without `BalancesBounded` on WETH9, or with a dirty `dst` address, Blaster finds
  counterexamples (or fails to prove the statement) for reasons that are real.
- **It finds real bugs.** In the Solidity documentation's `SimpleAuction`, bidding and
  ending overlap at `block.timestamp == auctionEndTime`: a bid can be accepted after the
  auction has paid out (see [examples.md](examples.md)). The counterexample to exact
  accounting led straight to it.
- **Single-call theorems need reachability facts.** They hold in every pre-state,
  including states no sequence of transactions produces, and some properties fail only
  there (an auction ended before its end time, a transaction marked executed but never
  submitted). Such facts are stated as hypotheses (`EndedInThePast`,
  `id < transactionCount`) or proved as invariants by induction (`MultiSig.Counted`).
- **Sequences of transactions** are handled in Lean: a single-call theorem holds in every
  chain state, so it holds for each call of any sequence, and properties of the whole
  sequence follow by induction (see [design.md](design.md)). Contract invariants that
  Blaster cannot state per call (e.g. "balances sum to the total supply") are assumed of
  the pre-state.
- **Blaster itself needed work.** Bitwise operators were unsupported, and two optimizer
  loops surfaced on ordinary compiled code (see [blaster-changes.md](blaster-changes.md)).
- **Limits.** Loops whose bound is symbolic and unconstrained unroll up to the fuel (a
  constrained bound is fine: infeasible longer paths are discharged). Gas is not modelled
  (sound for "every successful execution" properties: the model has more successful
  executions than the EVM). Callees do not re-enter. Contract creation, `DELEGATECALL`,
  `CALLCODE`, `SELFDESTRUCT` and `EXTCODECOPY` are outside the model.
- **Counterexamples are readable.** They list the environment and, for the world, every
  query the execution made with the solver's answer (storage slots, hashes, call
  outcomes), so a failing property comes with the chain state that breaks it.
- **Trust.** As with any `blaster` call, Z3 proofs are not reconstructed: the theorems rest
  on the `Blaster.Tactic.blasterProven` axiom, i.e. on Blaster's optimiser and translation
  and on Z3. The machine is validated against the Ethereum test suites and go-ethereum
  (see [testing.md](testing.md)), but it is not proved equivalent to a reference
  semantics.
