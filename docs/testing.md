# Testing

The test suites are isolated from the examples: every case exercises one aspect of the
machine or of compiled Solidity, either artificial or from the official Ethereum test
suites. `scripts/check-all.sh` checks them (with the examples), one file at a time; a
failing case is reported as `FAIL`.

| Suite | What it checks | How |
| --- | --- | --- |
| [`tests/Tests/Differential.lean`](../tests/Tests/Differential.lean) | The machine against go-ethereum on 226 concrete programs: every arithmetic/comparison/bitwise operator on all pairs of 20 edge-case operands, 80 random arithmetic programs, 40 random memory programs (overlapping `MSTORE`/`MSTORE8`/`MLOAD`/`MCOPY`), 30 calldata programs (unaligned and out-of-range loads, short inputs), storage and transient storage, keccak256 across block boundaries, execution context, jumps, stack limits, every kind of exceptional halt, calls | `#guard`: returned/reverted bytes, final storage and halting class must equal geth's |
| [`tests/Tests/Symbolic/Machine.lean`](../tests/Tests/Symbolic/Machine.lean) | Machine semantics for *all* inputs (14 theorems): wrap-around, byte-precise memory, copies, storage aliasing, computed jumps, hashing, value-carrying calls, unsupported instructions and fuel; plus 4 false claims Blaster must refute | Blaster, about 3 s |
| [`tests/Tests/Codegen/`](../tests/Tests/Codegen) | Compiled Solidity patterns (`tests/contracts/*.sol`, 19 theorems): packed storage slots (`Packed`), signed arithmetic and `int128` validation (`Signed`), `Error(string)` reverts and string returns (`Messages`), dynamic calldata arrays and loops with a caller-chosen length (`Dynamic`), encoding a call and decoding another contract's return data (`Caller`), loops over storage arrays (`Loop`) | Blaster, a few seconds per file |
| [`tests/Conformance/`](../tests/Conformance) | The machine against the official Ethereum test fixtures: 609 legacy VM tests and the Cancun general state tests (see below) | compiled runner (`lake exe conformance`), about 8 minutes |
| [`tests/Tests/Support/Keccak.lean`](../tests/Tests/Support/Keccak.lean) | The executable Keccak-256 used to answer the world's hash queries in concrete runs | `#guard` against geth / known digests |

## Conformance with the Ethereum test suites

`tests/Conformance/` is a compiled runner (`lake exe conformance`) that executes the
official Ethereum test fixtures with the machine's own `step` function and compares the
results with the expected ones. The fixtures are not in the repository (760 MB): fetch
them first, then run:

```bash
scripts/fetch-conformance-tests.sh
```

```bash
scripts/conformance.sh
```

The first script makes a sparse checkout of
[`ethereum/legacytests`](https://github.com/ethereum/legacytests) at a pinned commit into
`.lake/ethereum-tests`. The second builds and runs the runner under the same memory and CPU
limits as the proofs, and exits with status 1 if any test fails. `scripts/check-all.sh`
runs it too when the fixtures are present.

**What is run.**

- The legacy **VM tests** (`Constantinople/VMTests`, 609 tests) execute one piece of code
  in a given environment. The runner compares the storage and balance of the executing
  account, the return data, the hash of the logs, and the absence of calls.
- The **general state tests filled for Cancun** (the fork the machine models), in
  blockchain-test form: one transaction in a block on top of a pre-state. The runner
  derives the environment from the block header and the transaction: effective gas price,
  blob base fee, `PREVRANDAO`, the parent hash for `BLOCKHASH`. The world is the
  pre-state after the sender has paid for gas and value up front. The runner compares the
  storage and balance of the called account and the block's logs bloom.

**Verdicts.**

| Verdict | Meaning |
| --- | --- |
| pass | The machine's results equal the expected ones. |
| pass/OOG | The expected result is an exceptional halt, and the machine's execution provably runs out of gas. The runner adds up a lower bound on the gas each instruction is charged (memory expansion, copy and hash costs, EIP-2929 cold accesses, `SSTORE` metering, call costs; see [`Gas.lean`](../tests/Conformance/Gas.lean)). When that bound exceeds the gas available, the EVM ran out of gas on that execution. For state tests the block must also show that the transaction consumed all its gas. |
| inconclusive | Results differ, and the execution reads `GAS`. The machine leaves its value to the world, and these tests measure gas costs. |
| out of scope | The test needs what the machine does not model: an unsupported instruction (`CREATE*`, `DELEGATECALL`, `CALLCODE`, `SELFDESTRUCT`, `EXTCODECOPY`), a call into a contract or a precompile (only calls to accounts without code are answered exactly), contract creation, several transactions or blocks, or an invalid transaction. |
| FAIL | Any other difference. |

**Results** (fixtures at `ethereum/legacytests` `1f581b8c`):

| Fixtures | Tests | pass | pass/OOG | inconclusive | out of scope | FAIL |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| VM tests (Constantinople) | 609 | 572 | 30 | 2 | 5 | 0 |
| State tests (Cancun) | 10716 | 1641 | 1136 | 86 | 7853 | 0 |

The in-scope state tests cover:

- arithmetic, shifts, signed operations and comparisons;
- memory and `MCOPY`, transient storage, `PUSH0`;
- the environment opcodes (`SELFBALANCE`, `CHAINID`, `BASEFEE`, `BLOBHASH`, `BLOBBASEFEE`, `EXTCODEHASH`);
- every undefined opcode (`stBadOpcode`);
- `REVERT` and return data, calls to empty accounts with and without value;
- several hundred randomly generated programs (`stRandom*`).

The whole run takes about 8 minutes, half of it in a few performance tests that loop
millions of times.

**The runner catches machine bugs.** As a check, four plausible bugs were planted in the
machine together, each in a separate area:

- `SDIV` rounding towards −∞;
- `MSTORE8` writing the wrong byte;
- `SAR` by 256 or more saturating to the wrong sign;
- log topics in reverse order.

The runner reported 22 failures, in the arithmetic, memory, log and shift suites.

## Regenerating the differential corpus

`tests/Tests/Differential/Cases.lean` is generated; the expected outcomes come from geth's
reference interpreter (`evm run`, go-ethereum 1.14.12), not from this model:

```bash
GETH_EVM=/path/to/evm python3 tests/difftest/gen_cases.py
```

The corpus is seeded and deterministic. It avoids what the model abstracts on purpose: gas
(`GAS`, out-of-gas behaviour), contract creation, `DELEGATECALL`/`CALLCODE`/`SELFDESTRUCT`
and precompiles.

## Checking one file with per-goal timeouts

```bash
TIMEOUT=120 scripts/run-file.sh tests/Tests/Codegen/Packed.lean
```
