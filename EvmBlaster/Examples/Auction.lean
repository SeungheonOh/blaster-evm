import EvmBlaster
import Blaster

/-!
# `Auction`: the Solidity documentation's open auction

`contracts/Auction.sol` is the `SimpleAuction` example of the Solidity documentation, with
the same code: `beneficiary` (slot 0), `auctionEndTime` (slot 1), `highestBidder`
(slot 2), `highestBid` (slot 3), `pendingReturns` (mapping at slot 4), `ended` (slot 5).
Outbid bidders withdraw their own refunds; `auctionEnd` pays the highest bid to the
beneficiary.

Ether flows exactly as intended, except at one boundary. At
`block.timestamp == auctionEndTime`, `bid` (which rejects `>`) and `auctionEnd` (which
rejects `<`) are both allowed. A bid placed in the same block after `auctionEnd`:

- is accepted after the auction is over, and its Ether is stuck forever;
- credits the winner's bid, already paid to the beneficiary, back to the winner as a refund.

Blaster finds this as a counterexample to exact accounting ("every wei the contract
holds is owed to someone"). `contracts/AuctionFixed.sol` closes bidding from
`auctionEndTime` on, as the documentation's blind auction does, and satisfies it.
-/

namespace Examples.Auction
open Evm

#evm_contract_file Auction "contracts/build/Auction.bin-runtime"
#evm_contract_file AuctionFixed "contracts/build/AuctionFixed.bin-runtime"

def beneficiary (world : Query → Nat) : Nat := World.storage world 0 % U160
def endTime (world : Query → Nat) : Nat := World.storage world 1
def highestBidder (world : Query → Nat) : Nat := World.storage world 2 % U160
def highestBid (world : Query → Nat) : Nat := World.storage world 3

/-- The slot of `pendingReturns[a]`. -/
def pendingSlot (world : Query → Nat) (a : Nat) : Nat := world (.keccak 64 [a, 4])

/-- `ended` is the low byte of slot 5. -/
def endedIn (s : Nat → Nat) : Prop := s 5 % 256 ≠ 0

/-- What the contract owes in storage `s`, restricted to the accounts a call by `caller`
    can affect: the highest bid until it is paid out, and the refunds of the caller and of
    the highest bidder `prev` at the start of the call. -/
def owed (world : Query → Nat) (s : Nat → Nat) (caller prev : Nat) : Nat :=
  (if s 5 % 256 = 0 then s 3 else 0) + s (pendingSlot world caller)
    + (if prev = caller then 0 else s (pendingSlot world prev))

/-- A single-call theorem holds in every pre-state, including unreachable ones. An auction
    is only ever ended by `auctionEnd`, at or after the end time, and block timestamps
    never decrease: in a reachable state, an ended auction is called at or after the end
    time. -/
def EndedInThePast (env : Env) (world : Query → Nat) : Prop :=
  endedIn (World.storage world) → endTime world ≤ env.block.timestamp

/-- Exact accounting for one call: the balance moves exactly as the obligations do, and
    the refund of any other account `a` does not change. If the contract held exactly
    what it owed, it still does. -/
def ExactAccounting (env : Env) (world : Query → Nat) (a : Nat) (f : Frame) : Prop :=
  f.balance + owed world (World.storage world) env.msg.caller (highestBidder world) =
    env.balance + owed world (f.sload world) env.msg.caller (highestBidder world) ∧
  (a < U160 → a ≠ env.msg.caller → a ≠ highestBidder world →
    f.sload world (pendingSlot world a) = World.storage world (pendingSlot world a))

/-- The hashes of the call (to contract `c`) and `extra` do not collide. -/
abbrev Hashes (c : Contract) (env : Env) (world : Query → Nat) (extra : List HashInput) : Prop :=
  HashesFree c env world 3000 1 extra

/-- The refund entries exact accounting reads. -/
def accountKeys (env : Env) (world : Query → Nat) (a : Nat) : List HashInput :=
  [mapKey 4 env.msg.caller, mapKey 4 (highestBidder world), mapKey 4 a]

/-! ### Both versions -/

/-- Ether leaves only as the final payment (the highest bid, to the beneficiary, once the
    bidding time is over and before the auction is marked ended) or as a refund of exactly
    the caller's pending returns. -/
theorem ether_out (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    Hashes Auction env world [mapKey 4 env.msg.caller] →
    (execute Auction env world 3000).onSuccess (fun f =>
      AllCalls (fun c => c.value ≠ 0 →
        (c.to = beneficiary world ∧ c.value = highestBid world ∧
          ¬ endedIn (World.storage world) ∧ endTime world ≤ env.block.timestamp) ∨
        (c.to = env.msg.caller ∧
          c.value = World.storage world (pendingSlot world env.msg.caller))) f.calls) := by
  blaster

/-- The beneficiary and the end time are fixed, and an ended auction stays ended. -/
theorem settings_fixed (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    (execute Auction env world 3000).onSuccess (fun f =>
      f.sload world 0 = World.storage world 0 ∧ f.sload world 1 = World.storage world 1 ∧
      (endedIn (World.storage world) → endedIn (f.sload world))) := by
  blaster

/-- A new highest bid comes from the caller, with the value sent, above the previous one,
    no later than the end time. -/
theorem bids_are_real (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    (execute Auction env world 3000).onSuccess (fun f =>
      f.sload world 3 ≠ highestBid world →
        f.sload world 3 = env.msg.callvalue ∧ highestBid world < env.msg.callvalue ∧
        f.sload world 2 % U160 = env.msg.caller ∧ env.block.timestamp ≤ endTime world) := by
  blaster

/-- Liveness: an outbid bidder gets exactly their refund, if they accept the transfer. -/
theorem refund_succeeds (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    Hashes Auction env world [mapKey 4 env.msg.caller] →
    env.msg.calldata = .ofAbi 0x3ccfd60b [] → env.msg.callvalue = 0 →
    env.msg.caller ≠ env.msg.address →
    World.storage world (pendingSlot world env.msg.caller) ≤ env.balance →
    world (.callSuccess 0) ≠ 0 →
    (execute Auction env world 3000).succeedsWith (fun f =>
      f.valueSent = World.storage world (pendingSlot world env.msg.caller) ∧
      f.sload world (pendingSlot world env.msg.caller) = 0) := by
  blaster

/-! ### The boundary bug -/

-- The highest bid can change after the auction has ended, even in reachable states: a bid
-- at exactly the end time, after `auctionEnd`, is accepted.
#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat),
    env.WF → World.WF world → World.KeccakAbove world 6 →
    endedIn (World.storage world) → endTime world ≤ env.block.timestamp →
    (execute Auction env world 3000).onSuccess (fun f => f.sload world 3 = highestBid world)]

/-- The bug, stated positively: on an ended auction, a higher bid at exactly the end time
    succeeds. It becomes the highest bid, and the winner's bid, which `auctionEnd` already
    paid to the beneficiary, is credited back to the winner as a refund. (`ether_out` then
    shows that the late bid can never leave the contract: payouts need an auction not yet
    ended, refunds go to outbid bidders only.) -/
theorem late_bid_accepted (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    env.msg.calldata = .ofAbi 0x1998aeef [] →
    endedIn (World.storage world) → env.block.timestamp = endTime world →
    highestBid world < env.msg.callvalue → highestBid world ≠ 0 →
    World.storage world (pendingSlot world (highestBidder world)) + highestBid world < U256 →
    (execute Auction env world 3000).succeedsWith (fun f =>
      f.sload world 3 = env.msg.callvalue ∧ f.sload world 2 % U160 = env.msg.caller ∧
      f.sload world (pendingSlot world (highestBidder world)) =
        World.storage world (pendingSlot world (highestBidder world)) + highestBid world ∧
      endedIn (f.sload world)) := by
  blaster

/-- That boundary is the only exception: exact accounting holds for every call unless the
    auction has ended and the call happens at exactly the end time. -/
theorem accounting_except_at_end (env : Env) (world : Query → Nat) (a : Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    Hashes Auction env world (accountKeys env world a) →
    env.msg.caller ≠ env.msg.address → beneficiary world ≠ env.msg.address →
    EndedInThePast env world →
    ¬ (endedIn (World.storage world) ∧ env.block.timestamp = endTime world) →
    (execute Auction env world 3000).onSuccess (ExactAccounting env world a) := by
  blaster

/-! ### The fixed version -/

/-- `AuctionFixed`: exact accounting for every call. -/
theorem fixed_exact_accounting (env : Env) (world : Query → Nat) (a : Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    Hashes AuctionFixed env world (accountKeys env world a) →
    env.msg.caller ≠ env.msg.address → beneficiary world ≠ env.msg.address →
    EndedInThePast env world →
    (execute AuctionFixed env world 3000).onSuccess (ExactAccounting env world a) := by
  blaster

/-- `AuctionFixed`: once ended, the result is final. -/
theorem fixed_result_final (env : Env) (world : Query → Nat) :
    env.WF → World.WF world → World.KeccakAbove world 6 →
    endedIn (World.storage world) → endTime world ≤ env.block.timestamp →
    (execute AuctionFixed env world 3000).onSuccess (fun f =>
      f.sload world 3 = highestBid world ∧ f.sload world 2 = World.storage world 2) := by
  blaster

/-! ### The assumptions are consistent -/

#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (a : Nat),
    env.WF → World.WF world → World.KeccakAbove world 6 →
    Hashes Auction env world (accountKeys env world a) →
    env.msg.caller ≠ env.msg.address → beneficiary world ≠ env.msg.address →
    EndedInThePast env world → False]

end Examples.Auction
