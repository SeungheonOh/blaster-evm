# blaster-evm

Formal verification of Ethereum smart contracts with
[Blaster](https://github.com/input-output-hk/Lean-blaster), the SMT backend for Lean 4.

The EVM is written as an interpreter in Lean. A contract's compiled bytecode is loaded
as a constant, and Blaster executes the interpreter symbolically and hands what remains
to Z3. A theorem covers every caller, value, calldata and block, and every state of the
rest of the chain; assumptions about that state are explicit hypotheses.

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

## Examples

| Contract | Highlights |
| --- | --- |
| [Config](contracts/Config.sol) | only the owner changes the parameters, over any sequence of transactions |
| [Vault](contracts/Vault.sol) | Ether is released only to the beneficiary, after the deadline |
| [VaultBuggy](contracts/VaultBuggy.sol) | Blaster finds the planted `tx.origin` and deadline bugs |
| [Token](contracts/Token.sol) | only holders move balances; only the minter changes the supply |
| [WETH9](contracts/mainnet/WETH9.sol.txt) | **deployed mainnet bytecode**: Ether goes only to the caller, allowances are respected |
| [OZToken](contracts/OZToken.sol) | OpenZeppelin ERC20 + Ownable: access control, exact transfers |
| [OZPausableToken](contracts/OZPausableToken.sol) | OpenZeppelin ERC20 + Pausable + AccessControl: pausing freezes balances, roles are enforced |
| [Timelock](contracts/Timelock.sol) | a fee change is always announced two days in advance |
| [MultiSig](contracts/MultiSig.sol) | every payment was confirmed by two distinct owners |
| [Auction](contracts/Auction.sol) | **a bug in the Solidity documentation's example**: a bid accepted after the auction ended |

Details, including every property and timings: [docs/examples.md](docs/examples.md).

The machine is checked against the official Ethereum test suites (11,325 tests) and no
test fails. 3,379 agree with the expected results; 88 that measure gas costs are
inconclusive (gas is not modelled); the rest use features outside the model, mostly calls
into other contracts. More tests, against go-ethereum and of the symbolic semantics:
[docs/testing.md](docs/testing.md).

## Quick start

Requirements: Lean 4.24.0 (via elan) and Z3 on `PATH`.

```bash
scripts/check-all.sh
```

checks every proof file, one at a time and memory-capped. One file:

```bash
scripts/run-file.sh EvmBlaster/Examples/Vault.lean
```

More in [docs/running.md](docs/running.md).

## Documentation

- [docs/design.md](docs/design.md): how the EVM and the chain state are modelled
- [docs/examples.md](docs/examples.md): every example and its properties
- [docs/testing.md](docs/testing.md): test suites and Ethereum conformance
- [docs/findings.md](docs/findings.md): feasibility, limits, trust
- [docs/blaster-changes.md](docs/blaster-changes.md): changes to the vendored Blaster
- [docs/running.md](docs/running.md): running the checks

## Layout

```
EvmBlaster/            the EVM in Lean, spec helpers, #evm_contract
EvmBlaster/Examples/   proofs about the example contracts
contracts/             Solidity sources and compiled bytecode
tests/                 test suites and the conformance runner
scripts/               checking, compiling, fetching test fixtures
vendor/Lean-blaster/   vendored Blaster with local changes
docs/                  documentation
```
