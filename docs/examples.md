# Examples

## Solidity with UAL annotations

In [`examples/`](../examples), proved with `./blaster-evm` (see
[annotations.md](annotations.md)). Times are for the whole file, on one machine.

| Contract | Properties | Time |
| --- | --- | --- |
| [`Bank`](../examples/Bank.sol) | `deposit` credits exactly the caller and emits `Deposit`; `withdraw` pays the caller exactly the amount, which it had, and debits it; it touches no other balance; only the owner pauses; the owner never changes; solvency (the total deposits stay covered by the balance) is preserved by every call | 105 s |
| [`Token`](../examples/Token.sol) | ERC-20 with infinite approvals: `transfer` moves exactly the amount, keeps the two holdings' sum, touches no third balance, reverts without funds, keeps the supply; `approve` sets the allowance; `transferFrom` spends the allowance (unless infinite); only the owner mints | 22 s |
| [`Escrow`](../examples/Escrow.sol) | only the buyer pays, exactly the price; `release` pays the seller, `refund` (only by the arbiter) the buyer; a settled escrow stays settled; the parties never change; Ether goes only to the seller or the buyer, at most the price per call | 15 s |
| [`Vesting`](../examples/Vesting.sol) | a grant (a struct in a mapping, packed in two slots) is recorded exactly; a claim pays exactly what has vested, and the claimed amount never exceeds the grant; other grants are untouched; nothing can be claimed before the midpoint | 20 s |
| [`Crowdfund`](../examples/Crowdfund.sol) | contributions are recorded; the creator is paid once; refunds return the contribution; and two deliberate bugs found with counterexamples: the creator can claim before the deadline (`\|\|` for `&&`), and a refund does not clear the contribution | 9 s |

## Lean

Every theorem is about compiled bytecode, never the Solidity source. The proofs are in
[`EvmBlaster/Examples/`](../EvmBlaster/Examples), the contracts in
[`contracts/`](../contracts). Times are wall-clock per file on one machine.

| Contract | Bytecode | Properties | Time |
| --- | --- | --- | --- |
| [`Config`](../contracts/Config.sol) | solc 0.8.28 | only the owner changes the fee or the owner; `maxFee` is immutable; a new fee respects the cap; non-payable; no external calls; `setFee` works for the owner and reverts for anyone else; **over any sequence of calls in which the owner sends nothing, the owner and the fee never change** (Lean induction over the Blaster-proved single-call theorems) | 3 s |
| [`Vault`](../contracts/Vault.sol) | solc 0.8.28 | Ether leaves only towards the beneficiary, only after the deadline, at most one call per transaction; the deadline only moves forward and only by the owner; roles are immutable; balance accounting; the beneficiary *can* withdraw (liveness, assuming the recipient accepts the transfer) | 32 s |
| [`Token`](../contracts/Token.sol) | solc 0.8.28 | only the minter changes the supply; the minter is immutable; only the holder decreases a balance; `transfer` conserves and touches nothing else; `transfer` succeeds when funded; and the keccak assumptions are *needed* (counterexamples without them) | 6 s |
| [`VaultBuggy`](../contracts/VaultBuggy.sol) | solc 0.8.28 | Blaster finds the `tx.origin` phishing attack and the deadline-shortening bug as counterexamples | 2 s |
| **WETH9** ([source](../contracts/mainnet/WETH9.sol.txt)) | **deployed mainnet bytecode** (solc 0.4, 2017) | Ether leaves only towards the caller and is burned from the caller's WETH balance; incoming Ether is credited; nobody debits an account except its holder or a spender within its allowance, which is consumed; allowances change only by their owner or spender; `transfer` conserves; withdrawals succeed | 367 s |
| [`OZToken`](../contracts/OZToken.sol) | OpenZeppelin v5.1.0 ERC20 + Ownable, solc 0.8.28 | only the owner changes the supply or the owner; after renouncing, the supply is fixed forever; only the holder or a spender within its allowance debits an account; `transfer` and `approve` are exact | 27 s |
| [`Timelock`](../contracts/Timelock.sol) | solc 0.8.28 | the fee changes only when a queued change is due, and only to the queued value; only the admin queues; a change becomes executable exactly 2 days after it is queued; the fee stays within its cap; anyone can apply a due change; **over any sequence of calls without the admin, the fee keeps its value or takes the one already queued** (Lean induction) | 4 s |
| [`Auction`](../contracts/Auction.sol) | the Solidity documentation's `SimpleAuction`, solc 0.8.28 | Ether leaves only as the final payment to the beneficiary or as the caller's own refund; settings are fixed; bids are genuine; refunds succeed; a boundary bug (below) | 5 s |
| [`MultiSig`](../contracts/MultiSig.sol) | solc 0.8.28 | Ether leaves only through `execute`, to the recorded recipient with the recorded value, after two recorded confirmations; only owners confirm, for themselves; an executed transaction stays executed; confirmation counters stay exact; **from deployment, over any sequence of calls, every payment was confirmed by two distinct owners** (Lean induction) | 477 s |
| [`OZPausableToken`](../contracts/OZPausableToken.sol) | OpenZeppelin v5.1.0 ERC20 + Pausable + AccessControl, solc 0.8.28 | while paused, no balance and not the supply changes; only `PAUSER_ROLE` holders pause or unpause; only `MINTER_ROLE` holders mint; roles change only through the role's admin, or by renouncing; a pauser can always unpause | 417 s |

## Findings

**WETH9.** Two theorems surfaced genuine properties of the 2017 bytecode, which now appear
as explicit assumptions: it does not reject address arguments with dirty upper bits
(`balanceOf[dst mod 2^160]` is credited), and it adds to the recipient's balance without
an overflow check, which only the boundedness of the Ether supply makes safe.

**Auction.** In the Solidity documentation's `SimpleAuction`, `bid` rejects only
`block.timestamp > auctionEndTime` and `auctionEnd` only `block.timestamp <
auctionEndTime`: at exactly the end time both are allowed. A bid placed in the same block
after `auctionEnd` is accepted. Its Ether is stuck forever, and the winner's bid, already
paid to the beneficiary, is credited back to the winner as a refund. This is a proved
theorem about the original bytecode (`late_bid_accepted`); every other call keeps exact
accounting (every wei the contract holds is owed to someone).
[`AuctionFixed`](../contracts/AuctionFixed.sol) closes bidding at the end time, as the
documentation's blind auction does, and keeps exact accounting for every call.

**VaultBuggy.** Blaster finds two planted bugs as counterexamples: `extendLock`
authenticates with `tx.origin` (any contract the owner interacts with can act as the owner
and move the deadline), and it lacks the "never shorten" check.
