# blaster-evm

Formal verification of Ethereum smart contracts with
[Blaster](https://github.com/input-output-hk/Lean-blaster), the SMT backend for Lean 4.

The EVM is written as an interpreter in Lean. A contract's compiled bytecode is loaded
as a constant, and Blaster executes the interpreter symbolically and hands what remains
to Z3. A theorem covers every caller, value, calldata and block, and every state of the
rest of the chain; assumptions about that state are explicit hypotheses.

## Specifications in Solidity

Properties can be written next to the code, in the
[Universal Annotation Language](https://github.com/input-output-hk/UniversalAnnotationLanguage)
(UAL) of the Blaster team, and proved with one command:

```solidity
/*@ ONCHAIN [steps: 4000] withdraw : { uint256 : asAbi } -> () @*/
function withdraw(uint256 amount) external { ... }

/*@ PROPERTY withdraw_pays_the_caller :
  ∀ (amount : Nat) (env : Env) (world : World),
    let r := withdraw amount env world
    isSuccessful r →
      paidTo env.sender r = amount ∧
      Bank.balances (after world r) env.sender = Bank.balances (before world) env.sender - amount
@*/
```

```bash
./blaster-evm examples/Bank.sol
```

```
blaster-evm · examples/Bank.sol  (solc 0.8.28)
  Bank  1080 bytes · 3 ONCHAIN · 6 properties
    ✓ deposit_credits_the_caller           proved  0.5s
    ✓ withdraw_pays_the_caller             proved  13.7s
    ...
```

A false property gets a counterexample in Solidity terms: the call, the storage it read
(`contributions[msg.sender] = 32286`), what it did, and which part of the statement fails.
Parser, code generator, driver and reports are all Lean. See
[docs/annotations.md](docs/annotations.md).

| Example | Highlights |
| --- | --- |
| [Bank](examples/Bank.sol) | deposits and withdrawals are exact, other balances untouched, solvency, only the owner pauses |
| [Token](examples/Token.sol) | ERC-20: transfers are exact and touch nobody else, allowances are spent (infinite approvals excepted), only the owner mints |
| [Escrow](examples/Escrow.sol) | an enum state machine: settled is final, money goes only to the parties, at most the price is paid |
| [Vesting](examples/Vesting.sol) | structs in a mapping: claims pay exactly what has vested and never exceed the grant |
| [Crowdfund](examples/Crowdfund.sol) | two deliberate bugs, each caught with a readable counterexample |

## Lean examples

Theorems can also be stated directly in Lean, over the bytecode:

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

Requirements: Lean 4.24.0 (via elan) and Z3 on `PATH`. Annotated Solidity:

```bash
./blaster-evm examples/
```

Everything (test suites, Lean examples, annotated Solidity, conformance), one check at a
time and memory-capped:

```bash
scripts/check-all.sh
```

One Lean file:

```bash
scripts/run-file.sh EvmBlaster/Examples/Vault.lean
```

More in [docs/running.md](docs/running.md).

## Documentation

- [docs/annotations.md](docs/annotations.md): UAL annotations in Solidity and `./blaster-evm`
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
UAL/                   UAL for Solidity: grammar, EVM ledger API, #ual_property, the driver
examples/              Solidity contracts with UAL annotations
blaster-evm            the command (builds and runs UAL/Driver)
contracts/             Solidity sources and compiled bytecode
tests/                 test suites and the conformance runner
scripts/               checking, compiling, fetching test fixtures
vendor/Lean-blaster/   vendored Blaster with local changes
docs/                  documentation
```
