// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// An escrow between a buyer and a seller, with an arbiter: the buyer pays in, then either
/// the buyer (or the arbiter) releases the payment to the seller, or the arbiter refunds
/// the buyer.
contract Escrow {
    enum State { AwaitingPayment, AwaitingDelivery, Complete, Refunded }

    address public buyer;
    address public seller;
    address public arbiter;
    State public state;
    uint256 public price;

    error NotBuyer();
    error NotAllowed();
    error WrongState(State current);
    error WrongAmount(uint256 expected, uint256 got);

    event Paid(uint256 amount);
    event Released(address to, uint256 amount);
    event Refunded(address to, uint256 amount);

    constructor(address _seller, address _arbiter, uint256 _price) {
        buyer = msg.sender;
        seller = _seller;
        arbiter = _arbiter;
        price = _price;
    }

    /*@ PREDICATE
    /-- The escrow is settled: the payment went one way or the other. -/
    def settled (s : Snapshot) : Prop :=
      Escrow.state s = Escrow.State.Complete ∨ Escrow.state s = Escrow.State.Refunded

    /-- The parties of the escrow. -/
    def parties (s : Snapshot) : Nat × Nat × Nat := (Escrow.buyer s, Escrow.seller s, Escrow.arbiter s)
    @*/

    /*@ ONCHAIN pay : () @*/
    function pay() external payable {
        if (msg.sender != buyer) revert NotBuyer();
        if (state != State.AwaitingPayment) revert WrongState(state);
        if (msg.value != price) revert WrongAmount(price, msg.value);
        state = State.AwaitingDelivery;
        emit Paid(msg.value);
    }

    /*@ PROPERTY only_the_buyer_pays_the_price :
      ∀ (env : Env) (world : World),
        let r := pay env world
        isSuccessful r →
          env.sender = Escrow.buyer (before world) ∧ env.value = Escrow.price (before world) ∧
          Escrow.state (after world r) = Escrow.State.AwaitingDelivery
    @*/

    /*@ ONCHAIN release : () @*/
    function release() external {
        if (msg.sender != buyer && msg.sender != arbiter) revert NotAllowed();
        if (state != State.AwaitingDelivery) revert WrongState(state);
        state = State.Complete;
        payable(seller).transfer(price);
        emit Released(seller, price);
    }

    /*@ PROPERTY release_pays_the_seller :
      ∀ (env : Env) (world : World),
        let r := release env world
        isSuccessful r →
          paidTo (Escrow.seller (before world)) r = Escrow.price (before world) ∧
          Escrow.state (after world r) = Escrow.State.Complete
    @*/

    /*@ ONCHAIN refund : () @*/
    function refund() external {
        if (msg.sender != arbiter) revert NotAllowed();
        if (state != State.AwaitingDelivery) revert WrongState(state);
        state = State.Refunded;
        payable(buyer).transfer(price);
        emit Refunded(buyer, price);
    }

    /*@ PROPERTY only_the_arbiter_refunds :
      ∀ (env : Env) (world : World),
        let r := refund env world
        isSuccessful r →
          env.sender = Escrow.arbiter (before world) ∧
          paidTo (Escrow.buyer (before world)) r = Escrow.price (before world)
    @*/

    /*@ PROPERTY settled_is_final :
      ∀ (env : Env) (world : World),
        let r := dispatch env world
        settled (before world) → Escrow.state (after world r) = Escrow.state (before world)
    @*/

    /*@ PROPERTY the_parties_never_change :
      ∀ (env : Env) (world : World),
        parties (after world (dispatch env world)) = parties (before world)
    @*/

    /*@ PROPERTY money_goes_only_to_the_parties :
      ∀ (env : Env) (world : World) (a : Nat),
        let r := dispatch env world
        paidTo a r ≠ 0 → a = Escrow.seller (before world) ∨ a = Escrow.buyer (before world)
    @*/

    /*@ PROPERTY the_contract_pays_at_most_the_price :
      ∀ (env : Env) (world : World),
        sent (dispatch env world) ≤ Escrow.price (before world)
    @*/
}
