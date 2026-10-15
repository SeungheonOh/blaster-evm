# Annotations: specifications and proofs inside Solidity

`blaster-evm` proves properties written in Solidity comments, in the
[Universal Annotation Language](https://github.com/input-output-hk/UniversalAnnotationLanguage)
(UAL) of the Blaster team, against the contract's compiled bytecode:

```solidity
contract Bank {
    mapping(address => uint256) public balances;
    ...
    /*@ ONCHAIN [steps: 4000] withdraw : { uint256 : asAbi } -> () @*/
    function withdraw(uint256 amount) external { ... }

    /*@ PROPERTY withdraw_pays_the_caller :
      ∀ (amount : Nat) (env : Env) (world : World),
        let r := withdraw amount env world
        isSuccessful r →
          canWithdraw (before world) env.sender amount ∧
          paidTo env.sender r = amount ∧
          Bank.balances (after world r) env.sender = Bank.balances (before world) env.sender - amount
    @*/
}
```

```bash
./blaster-evm examples/Bank.sol
```

```
blaster-evm · examples/Bank.sol  (solc 0.8.28)
  Bank  1080 bytes · 3 ONCHAIN · 6 properties
    ✓ deposit_credits_the_caller           proved  0.5s
    ✓ withdraw_pays_the_caller             proved  13.7s
    ✓ withdraw_keeps_others_balances       proved  20.2s
    ✓ only_the_owner_pauses                proved  21.9s
    ✓ owner_never_changes                  proved  21.6s
    ✓ solvency_is_preserved                proved  22.2s

Summary: 6 proved  (104.6s)
```

The whole tool chain is Lean: the annotations are parsed by Lean's parser with the UAL
grammar (`UAL/Syntax.lean`), the driver (`UAL/Driver/`) compiles the file with solc,
generates Lean, and runs Blaster on each property, and the `#ual_property` command
(`UAL/Command.lean`) proves a property, or replays and decodes its counterexample.

## The command

```bash
./blaster-evm [prove] FILE.sol|DIR …   # prove every PROPERTY (the default command)
./blaster-evm check FILE.sol|DIR …     # only parse and type-check the annotations (seconds)
./blaster-evm list FILE.sol|DIR …      # list the annotations of each contract
./blaster-evm lean FILE.sol            # generate the Lean files and print where they are
./blaster-evm clean                    # remove generated files and cached results
```

A directory stands for the `.sol` files under it that have annotations. `prove` first
type-checks every statement (one Lean process for the file, a couple of seconds), then
proves the properties one at a time, each in its own Lean process with Blaster and Z3,
printing a line per property as it finishes, the counterexample or the error of each
property that fails, and a summary. While a property runs, a terminal shows which one and
for how long.

Options: `--only NAME` (properties whose name, or `Contract.name`, contains NAME;
repeatable), `--timeout S` (solver timeout per property, default 120), `--no-cache`,
`--json` (results as JSON on standard output), `--mem 8G` and `--cpu 400%` (limits of each
check), `-v` (show the Lean commands and their output).

The exit status is 0 when every property is proved, 1 when some property is falsified,
unknown or has an error, 2 for usage errors. Results are cached by the content of the
generated Lean (and the build of the tool): running again after editing one property
proves only that property; `(cached)` marks reused results.

Every check runs in a transient systemd scope with a memory cap (`MemoryMax`, default 8G,
no swap), a CPU quota and low priority, and one at a time on the machine (the checks share
a lock with `scripts/check-all.sh`). Ctrl-C stops the check and its solver.

**Requirements.** Lean (elan) and Z3 on `PATH`. The first run builds the tool (`lake build
blaster-evm UAL Blaster:shared`, under the same limits). The Solidity compiler is found
automatically: `$SOLC`, else a `solc` on `PATH` matching the file's `pragma solidity`, else
the newest matching release, downloaded once from binaries.soliditylang.org (checked
against its published SHA-256) into `~/.cache/blaster-evm/solc`.

## The annotation language

UAL annotations are delimited by `{-@ … @-}` in Haskell-like languages (Plinth, Aiken);
in Solidity they are block comments `/*@ … @*/`. Annotation bodies are Lean 4. There are
four kinds:

| UAL | Plinth (Cardano) | Solidity (EVM) |
| --- | --- | --- |
| `PREDICATE` | Lean definitions, in namespace `MPredicates` for module `M` | the same, in namespace `StemPredicates` for `Stem.sol` |
| `ONCHAIN` | marks an on-chain function, with its argument encodings and the Plutus version and budget | marks an external function, with its ABI types and encodings, the EVM version and a step bound |
| `PROPERTY` | a theorem about the on-chain functions, `blaster` by default, one Lean file per property | the same |
| `UPLC_DATA` | the `Data` encoding of a type | not applicable: data layouts come from the compiler (ABI, storage layout); rejected with a message |

### `PREDICATE`

```solidity
/*@ PREDICATE
/-- `who` has at least `amount` deposited. -/
def canWithdraw (s : Snapshot) (who amount : Nat) : Prop :=
  amount ≤ Bank.balances s who
@*/
```

Any Lean commands (`def`, `abbrev`, `theorem`, …). They go into namespace `BankPredicates`
for `Bank.sol` (opened in every property of the file). Predicates outside a contract see
the storage accessors of all contracts of the file; predicates inside a contract see its
own unqualified.

### `ONCHAIN`

```solidity
/*@ ONCHAIN [steps: 4000] withdraw : { uint256 : asAbi } -> () @*/
function withdraw(uint256 amount) external { ... }
```

The signature lists the argument types, then the return type (`()` for none), with UAL's
`{ Type : encoding }` notation; a bare type means encoding `asAbi`:

| Encoding | The Lean argument | Its calldata |
| --- | --- | --- |
| `asAbi` | the value as a Lean value of the Solidity type: `uintN`, `address`, `bytesN` are `Nat` (below `2^N`, `2^160`, `2^(8N)`), `bool` is `Bool`, `intN` is `Int` | its ABI encoding |
| `asWord` | any 256-bit word, as a `Nat` | the word as is (e.g. to test the contract's handling of dirty inputs) |

The signature is checked against the compiled ABI (a mismatch is an error that shows the
expected signature). Options: `[steps: N]` bounds the execution at N EVM steps (default
3000), in the role of UAL's Plutus execution budget (`[exCPU: …] [exMem: …]`, which is
rejected with a hint); `[version: Cancun]` is the EVM version (the only one modelled).

`ONCHAIN withdraw` in contract `Bank` gives the Lean function

```lean
Bank.withdraw (amount : Nat) (env : Env) (world : World) : Result
```

a message call to the contract with the ABI-encoded arguments, in environment `env` (the
caller, the value, the block) and chain state `world`. Every contract also has
`Bank.dispatch (env : Env) (world : World) : Result`, a call with arbitrary calldata
(`env.msg.calldata`): any function, or none, with any arguments. A property about
`dispatch` is about every call to the contract.

### `PROPERTY`

```solidity
/*@ PROPERTY name : statement [:= by tactic] @*/
```

A Lean proposition, usually quantified over the arguments, the environment and the
chain state. The default proof is Blaster; `:= by tactic` gives another one (with the
assumptions below as hypotheses).

## The EVM ledger API

What statements are written against (`UAL/Evm.lean`), in the role `CardanoLedgerApi` has
for Cardano:

| Name | Meaning |
| --- | --- |
| `Env` | a call environment: `env.sender`, `env.value`, `env.origin`, `env.timestamp`, `env.number`, `env.coinbase`, `env.self` (the contract), `env.balance` (its Ether before the call) |
| `World` | the chain state: the contract's storage, the other accounts, and the outcomes of the calls it makes |
| `Result` | the outcome of a call |
| `isSuccessful r`, `isReverted r` | the call succeeded; it reverted or halted (and had no effect) |
| `before world`, `after world r` | the contract's storage before the call, and after it (unchanged when it failed): a `Snapshot` |
| `C.x s` | state variable `x` of contract `C` in snapshot `s`: `Nat`, `Bool`, `Int`, or a structure for structs |
| `C.m s k`, `C.m s k1 k2` | mapping entries (`Bank.balances s who`, `Token.allowance s owner spender`) |
| `C.E.Member` | the value of an enum member (`Escrow.State.Complete`) |
| `C.Ev` | event `Ev`; `emits C.Ev r`: the call emitted it |
| `paidTo a r`, `sent r` | the Ether the call sent to `a`, and in total |
| `balanceAfter env r` | the contract's Ether after the call |

`./blaster-evm lean FILE` prints the generated `Contracts.lean`, which lists every name
of every contract with its type and storage location.

## What is assumed

`#ual_property` adds the assumptions of the model to the statement before proving it:

- each `env` is well-formed (words are 256 bits, addresses 160 bits, the calldata fits);
- each `world` is a valid chain state: its values are words, keccak256 hashes do not land
  on the slots of the plain state variables, `string`/`bytes` state variables hold short
  values;
- the arguments of every `ONCHAIN` call in the statement are values of their Solidity
  types;
- the keccak256 hashes the statement involves (those computed by its calls and those
  locating the mapping entries it reads) do not collide, and are far enough apart for the
  structs stored in mappings not to overlap.

  Only these hashes are assumed collision-free, not keccak256 as a whole: assuming an
  injective keccak256 into 256-bit values would be contradictory (there are more inputs
  than outputs), and would make every theorem vacuously true;
- outgoing calls do not re-enter the contract; their success and return data are
  arbitrary.

And it adds an obligation: every call in the statement stays within the model, i.e. it
finishes within its step bound and reaches no instruction the model leaves out (`CREATE`,
`DELEGATECALL`, …). A property about an execution the model does not cover fails, with a
counterexample saying why. Gas is not modelled: "every successful call satisfies P" is
sound (the model has more successful executions than the EVM), "this call succeeds" holds
up to running out of gas.

## Counterexamples

When a property is false, the counterexample's values are substituted into the statement,
every call in it is replayed on the EVM model, and the report shows, in Solidity terms:
the values of the statement's variables; which parts of the conclusion fail; and for each
call, the function and its arguments (decoded with the ABI), the caller and the block, the
storage it read before the call (named after the state variables, `m[k]` for mapping
entries, enum values by name), and the outcome (the storage changes, the Ether sent and
the events decoded from the ABI, or the revert reason: custom errors with their
arguments, `require` messages, panics).

From `examples/Crowdfund.sol`, which has two deliberate bugs:

```
    ✗ claim_only_after_a_successful_campaign   counterexample  0.8s
      examples/Crowdfund.sol:64
      64 │     /*@ PROPERTY claim_only_after_a_successful_campaign :
      65 │       ∀ (env : Env) (world : World),
      66 │         let r := claim env world
      67 │         isSuccessful r →
      68 │           Crowdfund.deadline (before world) ≤ env.timestamp ∧
      69 │           Crowdfund.goal (before world) ≤ Crowdfund.raised (before world)
      Counterexample
        env  msg.sender 0x…0000 · this 0x…5039 · balance 28101 wei
      Fails
        ✗ deadline (before world) ≤ env.timestamp
      Crowdfund.claim()
        from       0x…0000
        tx.origin  0x…22f1
        context    this 0x…5039 · balance 28101 wei · block 21655, timestamp 0
        storage    creator = msg.sender, deadline = 1, claimed = false, goal = 0, raised = 28101
        outcome    succeeds
                   claimed: false → true
                   sends 28101 wei to msg.sender
                   emits Claimed(amount: 28101)
```

## Errors

Parse errors, type errors and signature mismatches are reported at their position in the
Solidity file:

```
examples/Bank.sol:73:11: error: Unknown identifier `Bank.balance`
      73 │           Bank.balance (after world r) a = Bank.balances (before world) a
         │           ^
```

```
examples/Bank.sol:48:31: error: the ONCHAIN signature does not match the Solidity function
    48 │     /*@ ONCHAIN [steps: 4000] withdraw : address -> () @*/
       │                               ^
  hint: expected withdraw : uint256 -> ()
```

A property with an error is reported as such; the others are still proved.

## How it works

For `Stem.sol`, the driver generates, in `.lake/ual/gen/UALGen/Stem_<hash>/`:

- `Contracts.lean`: per contract, in namespace `C`, the bytecode (`#evm_contract_file`),
  the storage accessors (from the storage layout: packed fields, mappings, nested
  mappings, structs, enums), the events (from the ABI), and per `ONCHAIN` function `f` the
  Lean function `C.f` with its companions `f.inputs` (valid arguments), `f.hashes` (the
  keccak256 inputs of the call, for collision freedom) and `f.trace` (replays the call,
  `Evm.Replay.run`);
- `Predicates.lean`: the `PREDICATE` annotations;
- `Properties/C_name.lean`, one per property:

  ```lean
  #ual_property withdraw_pays_the_caller Bank.UALModel.info 120 :
        ∀ (amount : Nat) (env : Env) (world : World), …
  ```

Annotation text is copied with its lines and columns, so a position in a generated file
maps back to the Solidity file. The generated modules are compiled once and reused.
