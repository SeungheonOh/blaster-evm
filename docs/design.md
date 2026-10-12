# Design

The EVM is formalised as a Lean interpreter, in the way
[PlutusCoreBlaster](https://github.com/input-output-hk/PlutusCoreBlaster) formalises the
CEK machine. A contract's runtime bytecode is loaded as a constant, and
[Blaster](https://github.com/input-output-hk/Lean-blaster) executes the interpreter
symbolically and sends what remains to Z3.

## The machine ([`EvmBlaster/`](../EvmBlaster))

- [`Word.lean`](../EvmBlaster/Word.lean): 256-bit words as `Nat` with explicit `mod 2^256`
  arithmetic. Bitwise operators are `Nat.land`/`lor`/`xor`, which the vendored Blaster
  supports (see [blaster-changes.md](blaster-changes.md)).
- [`Instr.lean`](../EvmBlaster/Instr.lean): opcodes. Bytecode is decoded at elaboration
  time into a balanced search tree from program counters to instructions, so every fetch
  is resolved by constant folding in `O(log n)`.
- [`Memory.lean`](../EvmBlaster/Memory.lean): memory as the list of writes. A load at the
  offset of a store returns the stored word; other overlaps are assembled byte by byte
  (and the vendored Blaster merges the bytes of a word back into one field); copies and
  call outputs are recorded lazily.
- [`Machine.lean`](../EvmBlaster/Machine.lean): `step`, `run` (fuel-bounded) and
  `execute`, shaped like PlutusCoreBlaster's CEK machine. All opcodes up to Cancun except
  contract creation, `CALLCODE`, `DELEGATECALL`, `SELFDESTRUCT` and `EXTCODECOPY`, which
  halt in an `unsupported` state that no property accepts.
- [`Spec.lean`](../EvmBlaster/Spec.lean), [`Solidity.lean`](../EvmBlaster/Solidity.lean):
  `onSuccess`, `succeedsWith`, `isFailure`, mapping slots, short strings.
- [`Trace.lean`](../EvmBlaster/Trace.lean): `runCalls`, sequences of calls.
- [`Command.lean`](../EvmBlaster/Command.lean): `#evm_contract` / `#evm_contract_file`.

## Chain state and assumptions ([`Env.lean`](../EvmBlaster/Env.lean))

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
| `World.KeccakSpread world 4` | hashes of distinct inputs are at least 4 slots apart: a struct stored in a mapping (4 slots in `MultiSig`) never meets another hashed slot |
| `world (.callSuccess 0) ≠ 0` | the first outgoing call succeeds (e.g. the recipient is an EOA) |
| `Mainnet world`, `Deployed world` | the name and symbol slots hold what the constructor (or mainnet) stored |
| `BalancesBounded`, `SupplyBacked` | invariants of the contract assumed of the pre-state (balances backed by the Ether supply; balances sum to the total supply) |
| `EndedInThePast` (`Auction`) | reachability: an ended auction is only called at or after its end time, since block timestamps never decrease |
| `kec tx.2 = H` for every call (`MultiSig`) | across a sequence of transactions, keccak256 is one and the same function |

Outgoing calls are answered, not executed: the model assumes callees do not re-enter the
contract.

## Sequences of transactions

A single-call theorem holds in every chain state, so it holds for each call of any
sequence. [`runCalls`](../EvmBlaster/Trace.lean) makes a sequence explicit: each call sees
the storage left by the previous one, while everything else may change arbitrarily in
between. Properties of whole sequences then follow from single-call theorems by induction
in Lean (`Config.owner_and_fee_stable`, `Timelock.fee_without_admin`,
`MultiSig.payments_confirmed_by_two_owners`).

## Making Blaster execute it

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
