# Running

Requirements: Lean 4.24.0 (via elan), Z3 on `PATH` (tested with 4.13.3).

## Everything

```bash
scripts/check-all.sh
```

checks every test suite, example and Blaster's own bitwise tests, **one file at a time**,
and prints a line per file. Each check runs in a transient systemd unit capped at 8 GB of
memory and 4 cores, at low priority, and the unit (Z3 included) is stopped when the check
ends; checks are serialised by a lock. The limits are set by `CHECK_MEM`, `CHECK_CPU` and
`CHECK_RUNTIME` (see [`scripts/limits.sh`](../scripts/limits.sh)); `TIMEOUT` bounds every
SMT query (default 900 seconds).

Avoid `lake build Examples` and `lake test`: lake checks all files of a library at once,
each with its own Z3 processes.

## Annotated Solidity

```bash
./blaster-evm examples/
```

proves the UAL annotations of the Solidity files (see [annotations.md](annotations.md)),
under the same limits and lock.

## One file

With a timeout per SMT query:

```bash
TIMEOUT=600 scripts/run-file.sh EvmBlaster/Examples/WETH9.lean
```

## Conformance with the Ethereum test suites

The fixtures (760 MB) are fetched once into `.lake/`; `check-all.sh` then runs the
conformance suite too, or on its own:

```bash
scripts/fetch-conformance-tests.sh
```

```bash
scripts/conformance.sh
```

See [testing.md](testing.md) for what is compared and the results.

## Rebuilding

- After changing the vendored Blaster, rebuild its plugin with
  `lake build Blaster:shared` (`check-all.sh` does it).
- To recompile the contracts, set `SOLC` to a solc 0.8.28 binary and run
  `scripts/compile.sh`.
- To regenerate the differential corpus, see [testing.md](testing.md).
