# Test suites

Isolated from the examples: every case here is artificial, built to exercise one aspect of
the machine or of compiled Solidity. `scripts/check-all.sh` checks them (with the examples),
one file at a time; a failing case is reported as `FAIL`.

| Suite | What it checks | How |
| --- | --- | --- |
| `Tests/Differential.lean` | The machine against go-ethereum on 226 concrete programs: every arithmetic/comparison/bitwise operator on all pairs of 20 edge-case operands, 80 random arithmetic programs, 40 random memory programs (overlapping `MSTORE`/`MSTORE8`/`MLOAD`/`MCOPY`), 30 calldata programs (unaligned and out-of-range loads, short inputs), storage and transient storage, keccak256 across block boundaries, execution context, jumps, stack limits, every kind of exceptional halt, calls | `#guard`: returned/reverted bytes, final storage and halting class must equal geth's |
| `Tests/Symbolic/Machine.lean` | Machine semantics for *all* inputs (14 theorems): wrap-around, byte-precise memory, copies, storage aliasing, computed jumps, hashing, value-carrying calls, unsupported instructions and fuel; plus 4 false claims Blaster must refute | Blaster, about 3 s |
| `Tests/Codegen/*.lean` | Compiled Solidity patterns (`tests/contracts/*.sol`, 19 theorems): packed storage slots (`Packed`), signed arithmetic and `int128` validation (`Signed`), `Error(string)` reverts and string returns (`Messages`), dynamic calldata arrays and loops with a caller-chosen length (`Dynamic`), encoding a call and decoding another contract's return data (`Caller`), loops over storage arrays (`Loop`) | Blaster, a few seconds per file |
| `Tests/Support/Keccak.lean` | The executable Keccak-256 used to answer the world's hash queries in concrete runs | `#guard` against geth / known digests |

## Regenerating the differential corpus

`Tests/Differential/Cases.lean` is generated; the expected outcomes come from geth's
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
