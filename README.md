# blaster-evm: verifying EVM bytecode with Blaster

A prototype that applies [Blaster](https://github.com/input-output-hk/Lean-blaster), the
SMT backend for Lean 4, to Ethereum smart contracts, in the way
[PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster) applies it to
Cardano validators: the EVM is formalised as a Lean interpreter, a contract's **runtime
bytecode** is loaded as a constant, and Blaster executes the interpreter symbolically
and sends what remains to Z3. A theorem quantifies over every caller, value, calldata,
block, and every state of the rest of the chain, with explicit assumptions about that
state.

```lean
#evm_contract_file Vault "contracts/build/Vault.bin-runtime"

/-- Ether only leaves the contract when the beneficiary asks, after the deadline. -/
theorem transfers_only_after_unlock (env : Env) (world : Query → Nat) :
    env.WF → World.WF world →
    (execute Vault env world 3000).onSuccess (fun f =>
      f.valueSent ≠ 0 →
        env.msg.caller = beneficiary world ∧ unlockTime world ≤ env.block.timestamp) := by
  blaster
```

## Results

Every theorem is about compiled bytecode, never the Solidity source. Times are wall-clock
per file on one machine.

| Contract | Bytecode | Properties | Time |
| --- | --- | --- | --- |
| [`Config`](contracts/Config.sol) | solc 0.8.28 | only the owner changes the fee or the owner; `maxFee` is immutable; a new fee respects the cap; non-payable; no external calls; `setFee` works for the owner and reverts for anyone else; **over any sequence of calls in which the owner sends nothing, the owner and the fee never change** (Lean induction over the Blaster-proved single-call theorems) | 4 s |
| [`Vault`](contracts/Vault.sol) | solc 0.8.28 | Ether leaves only towards the beneficiary, only after the deadline, at most one call per transaction; the deadline only moves forward and only by the owner; roles are immutable; balance accounting; the beneficiary *can* withdraw (liveness, assuming the recipient accepts the transfer) | 40 s |
| [`Token`](contracts/Token.sol) | solc 0.8.28 | only the minter changes the supply; the minter is immutable; only the holder decreases a balance; `transfer` conserves and touches nothing else; `transfer` succeeds when funded; and the keccak assumptions are *needed* (counterexamples without them) | 10 s |
| [`VaultBuggy`](contracts/VaultBuggy.sol) | solc 0.8.28 | Blaster finds the `tx.origin` phishing attack and the deadline-shortening bug as counterexamples | 3 s |
| **WETH9** ([source](contracts/mainnet/WETH9.sol.txt)) | **deployed mainnet bytecode** (solc 0.4, 2017) | Ether leaves only towards the caller and is burned from the caller's WETH balance; incoming Ether is credited; nobody debits an account except its holder or a spender within its allowance, which is consumed; allowances change only by their owner or spender; `transfer` conserves; withdrawals succeed | 508 s |
| [`OZToken`](contracts/OZToken.sol) | OpenZeppelin v5.1.0 ERC20 + Ownable, solc 0.8.28 | only the owner changes the supply or the owner; after renouncing, the supply is fixed forever; only the holder or a spender within its allowance debits an account; `transfer` and `approve` are exact | 51 s |

Two of WETH9's theorems surfaced genuine properties of the 2017 bytecode, which now appear
as explicit assumptions: it does not reject address arguments with dirty upper bits
(`balanceOf[dst mod 2^160]` is credited), and it adds to the recipient's balance without
an overflow check, which only the boundedness of the Ether supply makes safe.

The isolated [test suites](tests/README.md) check the machine itself: 226 artificial
programs against go-ethereum's reference interpreter, symbolic semantics of artificial
programs, and Solidity code-generation patterns (packed storage, signed arithmetic, revert
reasons, dynamic calldata, cross-contract calls, loops).

## How it works

### The machine ([`EvmBlaster/`](EvmBlaster))

- [`Word.lean`](EvmBlaster/Word.lean): 256-bit words as `Nat` with explicit `mod 2^256`
  arithmetic. Bitwise operators are `Nat.land`/`lor`/`xor`, which the vendored Blaster
  supports (see below).
- [`Instr.lean`](EvmBlaster/Instr.lean): opcodes; bytecode is decoded at elaboration time
  into a balanced search tree from program counters to instructions, so every fetch is
  resolved by constant folding in `O(log n)`.
- [`Memory.lean`](EvmBlaster/Memory.lean): memory as the list of writes. A load at the
  offset of a store returns the stored word; other overlaps are assembled byte by byte
  (and the vendored Blaster merges the bytes of a word back into one field); copies and
  call outputs are recorded lazily.
- [`Machine.lean`](EvmBlaster/Machine.lean): `step`, `run` (fuel-bounded) and `execute`,
  shaped like PlutusCoreBlaster's CEK machine. All opcodes up to Cancun except contract
  creation, `CALLCODE`, `DELEGATECALL`, `SELFDESTRUCT` and `EXTCODECOPY`, which halt in an
  `unsupported` state that no property accepts.
- [`Spec.lean`](EvmBlaster/Spec.lean), [`Solidity.lean`](EvmBlaster/Solidity.lean):
  `onSuccess`, `succeedsWith`, `isFailure`, mapping slots, short strings.
- [`Command.lean`](EvmBlaster/Command.lean): `#evm_contract` / `#evm_contract_file`.

### Chain state and assumptions ([`Env.lean`](EvmBlaster/Env.lean))

An execution is a function of two inputs:

- `env : Env`, first-order data: block, transaction, message (caller, value, calldata),
  the contract's balance;
- `world : Query → Nat`, the chain state. Every impure read is a query answered by the
  world: the contract's initial storage, `keccak256`, other accounts' balances and code,
  block hashes, and the outcome and return data of each outgoing call.

Theorems are universally quantified over both, so assumptions about the chain are ordinary
hypotheses about the world. The examples use, for instance:

| Assumption | Meaning |
| --- | --- |
| `World.WF world`, `env.WF` | every value is a 256-bit word, addresses are 160 bits |
| `World.KeccakInjective`, `World.KeccakAbove 5` | idealised collision resistance; hashes avoid the low storage slots |
| `world (.callSuccess 0) ≠ 0` | the first outgoing call succeeds (e.g. the recipient is an EOA) |
| `Mainnet world` | WETH9's name and symbol slots hold their mainnet values |
| `BalancesBounded`, `SupplyBacked` | invariants of the contract assumed of the pre-state (balances backed by the Ether supply; balances sum to the total supply) |

Outgoing calls are answered, not executed: the model assumes callees do not re-enter the
contract.

### Making Blaster execute it

The EVM had to be shaped for Blaster's optimiser; these are the rules, with the reason for
each:

- Blaster unrolls a recursive call only if every explicit argument is constructor-headed.
  The machine state therefore carries the code and environment (`State.running c env world
  f`), and recursive helpers box their non-structural arguments in `Box`, a
  single-constructor `inductive`: a `structure` constructor only counts when all of its
  fields are constructors.
- No type abbreviations in function types (`Query → Nat` is written out), no
  function-typed structure fields, no inductive predicates (`∀ a ∈ l` becomes a recursive
  `Prop`): Blaster's SMT translation does not handle these yet.
- Keep symbolic case splits out of arithmetic. Blaster pushes operations into the branches
  of an if-then-else, so a sum of `k` case splits grows like `2^k`. Byte positions are
  therefore powers `2 ^ (8 * k)` (opaque to the optimiser) rather than lookup tables, and
  the memory model avoids symbolic lengths where it can: a call's output area is recorded
  with its literal length (the return data overlays a prefix of it). A reader that split
  overlapping reads into segments was tried and dropped: with symbolic offsets (after any
  dynamic allocation) its terms grew exponentially, while the byte-wise reader stays
  linear and the field-merging rule recovers compact terms when offsets are literals.
- Recursive functions keep a single recursive case (per-case logic lives in a
  non-recursive helper): Lean's equation generator, which Blaster calls, overflows the
  stack on many-armed structural recursion.

## Changes to Blaster

Blaster is vendored in [`vendor/Lean-blaster`](vendor) (details and the exact upstream
revision in [`vendor/UPSTREAMS.md`](vendor/UPSTREAMS.md); full diff in
`vendor/Lean-blaster.patch`). All changes are general-purpose rewrite rules for `Nat`, not
EVM-specific:

1. **Bitwise operators.** Upstream unfolds `&&&`, `|||`, `^^^` into well-founded recursion
   it cannot translate. They are now opaque. A small bit-support analysis (which bit
   positions a term may set, from literals, `% 2^k`, `/ 2^k`, `* 2^k`, disjoint sums and
   bound hypotheses) drives the rewrites: `x &&& N` for a literal mask becomes a sum of
   bit-range extracts (one per run of ones in `N`), and `|||`/`^^^` of operands with
   disjoint bits become `+`. Whatever remains gets exact recursive SMT definitions.
2. **Bit fields.** With the same analysis, `% 2^k` drops the addends of a sum that are
   multiples of `2^k`, `/ 2^k` divides them separately, and both vanish on terms below
   `2^k`. Writing a packed storage field and reading it (or its neighbours) back then
   simplifies to the expected values before the solver is called. (These rules build
   their results directly instead of asking the optimizer for a restart: a restart inside
   an `if-then-else` branch can re-run the rule on the original branch forever.)
3. **Merging bit fields**: adjacent fields of the same value in a sum,
   `((x / 2^p) % 2^w) * 2^q + ((x / 2^(p+w)) % 2^v) * 2^(q+w)`, become one field, so a
   word read byte by byte from memory collapses back into (a slice of) the stored word.
4. **`x % n = x` under a hypothesis `x < n`**, e.g. an address masked to 160 bits.

They come with tests in `vendor/Lean-blaster/Tests/Smt/SmtNat/SmtNatBitwise.lean`,
including false near-miss statements the rewrites must not prove. Their effect on this
project: the packed-storage suite went from not finishing in 20 minutes to 4 seconds.

## Feasibility: what we learned

- **It works on real bytecode.** Solidity's dispatcher, ABI decoding (including dynamic
  arrays), checked arithmetic, custom errors, revert strings, packed storage, mappings,
  events and external calls all execute symbolically. Typical properties over *all*
  calldata take 1 to 30 seconds; properties quantifying over all holders of a mapping
  take minutes.
- **Word arithmetic as `Nat` is adequate** once bitwise operators are supported. Masks and
  shifts by constants stay linear; the remaining hard cases are byte-level reasoning
  (addressed by merging byte fields back into words) and quantifiers over mapping keys.
- **The chain-state oracle is the right interface.** Every assumption is visible in the
  theorem, and several examples show why they matter: without the keccak assumptions,
  without `BalancesBounded` on WETH9, or with a dirty `dst` address, Blaster finds
  counterexamples (or fails to prove the statement) for reasons that are real.
- **Sequences of transactions** are handled in Lean: a single-call theorem holds in
  every chain state, so it holds for each call of any sequence, and properties of the
  whole sequence follow by induction (`runCalls` in [`Trace.lean`](EvmBlaster/Trace.lean),
  `owner_and_fee_stable` in the Config example). Contract invariants that Blaster cannot
  state per call (e.g. "balances sum to the total supply") are assumed of the pre-state.
- **Limits.** Loops whose bound is symbolic and unconstrained unroll up to the fuel (a
  constrained bound is fine: infeasible longer paths are discharged). Gas is not modelled
  (sound for "every successful execution" properties: the model has more successful
  executions than the EVM). Callees do not re-enter. Counterexamples show the world as an
  opaque function; naming the relevant world values as variables makes them visible (see
  `VaultBuggy`).
- **Trust.** As with any `blaster` call, Z3 proofs are not reconstructed: the theorems rest
  on the `Blaster.Tactic.blasterProven` axiom, i.e. on Blaster's optimiser and translation
  and on Z3. The machine is validated against go-ethereum on 226 programs, but it is not
  proved equivalent to a reference semantics.

## Layout

```
EvmBlaster/            the formal EVM, spec helpers, #evm_contract
EvmBlaster/Examples/   properties of Config, Vault, VaultBuggy, Token, WETH9, OZToken
contracts/             Solidity sources, compiled runtime bytecode (build/),
                       OpenZeppelin v5.1.0 sources (lib/), WETH9 mainnet bytecode (mainnet/)
tests/                 isolated test suites (see tests/README.md)
scripts/               check-all.sh, run-file.sh, limits.sh, compile.sh
vendor/Lean-blaster/   vendored Blaster with local changes
```

## Running

Requirements: Lean 4.24.0 (via elan), Z3 on `PATH` (tested with 4.13.3).

```bash
scripts/check-all.sh
```

checks every test suite, example and Blaster's own bitwise tests, **one file at a time**,
and prints a line per file. Each check runs in a transient systemd unit capped at 8 GB of
memory and 4 cores, at low priority, and the unit (Z3 included) is stopped when the check
ends; checks are serialised by a lock. The limits are set by `CHECK_MEM` and `CHECK_CPU`
(see [`scripts/limits.sh`](scripts/limits.sh)). Avoid `lake build Examples` and
`lake test`: lake checks all files of a library at once, each with its own Z3 processes.

One file, with a timeout per SMT query:

```bash
TIMEOUT=600 scripts/run-file.sh EvmBlaster/Examples/WETH9.lean
```

After changing the vendored Blaster, rebuild its plugin with `lake build Blaster:shared`
(`check-all.sh` does it). To recompile the contracts, set `SOLC` to a solc 0.8.28 binary
and run `scripts/compile.sh`.
