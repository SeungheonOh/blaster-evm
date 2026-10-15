// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// Token-less vesting: the admin grants Ether to a beneficiary, which vests half at the
/// midpoint of the grant's duration and in full at its end; the beneficiary claims what
/// has vested.
contract Vesting {
    struct Grant {
        uint128 total;
        uint128 claimed;
        uint64 start;
        uint64 duration;
    }

    address public admin;
    uint256 public outstanding;
    mapping(address => Grant) public grants;

    error NotAdmin();
    error GrantExists();
    error BadDuration();
    error NothingToClaim();

    event Granted(address indexed who, uint256 total, uint64 duration);
    event Claimed(address indexed who, uint256 amount);

    constructor() {
        admin = msg.sender;
    }

    /*@ PREDICATE
    /-- What `g` has vested at time `t`. -/
    def vestedAt (g : Vesting.Grant) (t : Nat) : Nat :=
      if g.start + g.duration ≤ t then g.total
      else if g.start + g.duration / 2 ≤ t then g.total / 2
      else 0

    /-- A grant never pays out more than it holds. -/
    def sound (g : Vesting.Grant) : Prop := g.claimed ≤ g.total
    @*/

    /*@ ONCHAIN grant : address -> uint64 -> () @*/
    function grant(address who, uint64 duration) external payable {
        if (msg.sender != admin) revert NotAdmin();
        if (grants[who].total != 0) revert GrantExists();
        if (duration == 0) revert BadDuration();
        grants[who] = Grant(uint128(msg.value), 0, uint64(block.timestamp), duration);
        outstanding += msg.value;
        emit Granted(who, msg.value, duration);
    }

    /*@ PROPERTY grant_records_the_grant :
      ∀ (who duration : Nat) (env : Env) (world : World),
        let r := grant who duration env world
        isSuccessful r → env.value < 2 ^ 128 → env.timestamp < 2 ^ 64 →
          (Vesting.grants (after world r) who).total = env.value ∧
          (Vesting.grants (after world r) who).claimed = 0 ∧
          (Vesting.grants (after world r) who).start = env.timestamp ∧
          (Vesting.grants (after world r) who).duration = duration ∧
          Vesting.outstanding (after world r) = Vesting.outstanding (before world) + env.value
    @*/

    function vested(Grant memory g, uint256 t) internal pure returns (uint256) {
        if (t >= uint256(g.start) + g.duration) return g.total;
        if (t >= uint256(g.start) + g.duration / 2) return g.total / 2;
        return 0;
    }

    /*@ ONCHAIN [steps: 4000] claim : () @*/
    function claim() external {
        Grant storage g = grants[msg.sender];
        uint256 amount = vested(g, block.timestamp) - g.claimed;
        if (amount == 0) revert NothingToClaim();
        g.claimed += uint128(amount);
        outstanding -= amount;
        payable(msg.sender).transfer(amount);
        emit Claimed(msg.sender, amount);
    }

    /*@ PROPERTY claim_pays_what_has_vested :
      ∀ (env : Env) (world : World),
        let r := claim env world
        let g := Vesting.grants (before world) env.sender
        isSuccessful r →
          paidTo env.sender r = vestedAt g env.timestamp - g.claimed ∧
          (Vesting.grants (after world r) env.sender).claimed = vestedAt g env.timestamp
    @*/

    /*@ PROPERTY claims_stay_within_the_grant :
      ∀ (env : Env) (world : World),
        let r := claim env world
        sound (Vesting.grants (before world) env.sender) →
          sound (Vesting.grants (after world r) env.sender)
    @*/

    /*@ PROPERTY claim_leaves_other_grants_alone :
      ∀ (env : Env) (world : World) (a : Nat),
        let r := claim env world
        a < 2 ^ 160 → a ≠ env.sender →
          Vesting.grants (after world r) a = Vesting.grants (before world) a
    @*/

    /*@ PROPERTY nothing_vests_before_the_midpoint :
      ∀ (env : Env) (world : World),
        let g := Vesting.grants (before world) env.sender
        env.timestamp < g.start + g.duration / 2 → isReverted (claim env world)
    @*/
}
