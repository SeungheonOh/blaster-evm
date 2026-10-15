// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// A crowdfunding campaign. It has two deliberate bugs, which two of its properties catch:
/// `claim` checks `||` where it should check `&&`, and `refund` forgets to clear the
/// contribution. Run `./blaster-evm examples/Crowdfund.sol` to see the counterexamples.
contract Crowdfund {
    address public creator;
    uint64 public deadline;
    uint256 public goal;
    uint256 public raised;
    bool public claimed;
    mapping(address => uint256) public contributions;

    error TooLate();
    error TooEarly();
    error NotCreator();
    error GoalNotReached(uint256 raised, uint256 goal);
    error GoalReached();
    error NothingToRefund();
    error AlreadyClaimed();

    event Contributed(address indexed who, uint256 amount);
    event Claimed(uint256 amount);
    event Refunded(address indexed who, uint256 amount);

    constructor(uint64 _deadline, uint256 _goal) {
        creator = msg.sender;
        deadline = _deadline;
        goal = _goal;
    }

    /*@ ONCHAIN contribute : () @*/
    function contribute() external payable {
        if (block.timestamp >= deadline) revert TooLate();
        contributions[msg.sender] += msg.value;
        raised += msg.value;
        emit Contributed(msg.sender, msg.value);
    }

    /*@ PROPERTY contributions_are_recorded :
      ∀ (env : Env) (world : World),
        let r := contribute env world
        isSuccessful r →
          env.timestamp < Crowdfund.deadline (before world) ∧
          Crowdfund.contributions (after world r) env.sender =
            Crowdfund.contributions (before world) env.sender + env.value ∧
          Crowdfund.raised (after world r) = Crowdfund.raised (before world) + env.value
    @*/

    /*@ ONCHAIN claim : () @*/
    function claim() external {
        if (msg.sender != creator) revert NotCreator();
        if (claimed) revert AlreadyClaimed();
        // BUG: should be `&&`: the creator can claim before the deadline
        if (block.timestamp < deadline || raised < goal) {
            if (raised < goal) revert GoalNotReached(raised, goal);
        }
        claimed = true;
        payable(creator).transfer(raised);
        emit Claimed(raised);
    }

    /*@ PROPERTY claim_only_after_a_successful_campaign :
      ∀ (env : Env) (world : World),
        let r := claim env world
        isSuccessful r →
          Crowdfund.deadline (before world) ≤ env.timestamp ∧
          Crowdfund.goal (before world) ≤ Crowdfund.raised (before world)
    @*/

    /*@ PROPERTY claim_pays_the_creator_once :
      ∀ (env : Env) (world : World),
        let r := claim env world
        isSuccessful r →
          ¬ Crowdfund.claimed (before world) ∧ Crowdfund.claimed (after world r) ∧
          paidTo (Crowdfund.creator (before world)) r = Crowdfund.raised (before world)
    @*/

    /*@ ONCHAIN refund : () @*/
    function refund() external {
        if (block.timestamp < deadline) revert TooEarly();
        if (raised >= goal) revert GoalReached();
        uint256 amount = contributions[msg.sender];
        if (amount == 0) revert NothingToRefund();
        // BUG: forgets `contributions[msg.sender] = 0;`
        payable(msg.sender).transfer(amount);
        emit Refunded(msg.sender, amount);
    }

    /*@ PROPERTY refund_returns_the_contribution :
      ∀ (env : Env) (world : World),
        let r := refund env world
        isSuccessful r →
          paidTo env.sender r = Crowdfund.contributions (before world) env.sender
    @*/

    /*@ PROPERTY refund_clears_the_contribution :
      ∀ (env : Env) (world : World),
        let r := refund env world
        isSuccessful r → Crowdfund.contributions (after world r) env.sender = 0
    @*/

    /*@ PROPERTY the_creator_never_changes :
      ∀ (env : Env) (world : World),
        Crowdfund.creator (after world (dispatch env world)) = Crowdfund.creator (before world)
    @*/
}
