// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// The `SimpleAuction` example of the Solidity documentation (docs/examples/blind-auction.rst,
/// v0.8.28), with the same code. Bidders send their bids; outbid bidders withdraw their own
/// refunds ("withdrawal pattern"); once the bidding time is over, anyone ends the auction,
/// which pays the highest bid to the beneficiary.
///
/// At `block.timestamp == auctionEndTime` both `bid` and `auctionEnd` are allowed: a bid
/// can be accepted after the auction has ended (see `EvmBlaster/Examples/Auction.lean`).
contract Auction {
    error AuctionAlreadyEnded();
    error BidNotHighEnough(uint256 highestBid);
    error AuctionNotYetEnded();
    error AuctionEndAlreadyCalled();

    address payable public beneficiary;  // slot 0
    uint256 public auctionEndTime;       // slot 1
    address public highestBidder;        // slot 2
    uint256 public highestBid;           // slot 3
    mapping(address => uint256) pendingReturns;  // slot 4
    bool ended;                          // slot 5

    event HighestBidIncreased(address bidder, uint256 amount);
    event AuctionEnded(address winner, uint256 amount);

    constructor(uint256 biddingTime, address payable beneficiaryAddress) {
        beneficiary = beneficiaryAddress;
        auctionEndTime = block.timestamp + biddingTime;
    }

    /// Bid with the value sent. The previous highest bid becomes refundable.
    function bid() external payable {
        if (block.timestamp > auctionEndTime) revert AuctionAlreadyEnded();
        if (msg.value <= highestBid) revert BidNotHighEnough(highestBid);
        if (highestBid != 0) {
            pendingReturns[highestBidder] += highestBid;
        }
        highestBidder = msg.sender;
        highestBid = msg.value;
        emit HighestBidIncreased(msg.sender, msg.value);
    }

    /// Withdraw a bid that was overbid.
    function withdraw() external returns (bool) {
        uint256 amount = pendingReturns[msg.sender];
        if (amount > 0) {
            pendingReturns[msg.sender] = 0;
            if (!payable(msg.sender).send(amount)) {
                pendingReturns[msg.sender] = amount;
                return false;
            }
        }
        return true;
    }

    /// End the auction and send the highest bid to the beneficiary.
    function auctionEnd() external {
        if (block.timestamp < auctionEndTime) revert AuctionNotYetEnded();
        if (ended) revert AuctionEndAlreadyCalled();
        ended = true;
        emit AuctionEnded(highestBidder, highestBid);
        beneficiary.transfer(highestBid);
    }
}
