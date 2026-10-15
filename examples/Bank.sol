// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/*@ PREDICATE
/-- `who` has at least `amount` deposited. -/
def canWithdraw (s : Snapshot) (who amount : Nat) : Prop :=
  amount ≤ Bank.balances s who

/-- Every value an address can take. -/
def isAddress (a : Nat) : Prop := a < 2 ^ 160
@*/

/// A bank: customers deposit and withdraw Ether; the owner can pause withdrawals.
contract Bank {
    address public owner;          // slot 0
    bool public paused;            // slot 0, byte 20 (packed with owner)
    uint256 public totalDeposits;  // slot 1
    mapping(address => uint256) public balances;  // slot 2

    error NotOwner();
    error Paused();
    error Insufficient(uint256 available);
    error TransferFailed();

    event Deposit(address indexed who, uint256 amount);
    event Withdrawal(address indexed who, uint256 amount);

    constructor() {
        owner = msg.sender;
    }

    /*@ ONCHAIN deposit : () @*/
    function deposit() external payable {
        balances[msg.sender] += msg.value;
        totalDeposits += msg.value;
        emit Deposit(msg.sender, msg.value);
    }

    /*@ PROPERTY deposit_credits_the_caller :
      ∀ (env : Env) (world : World),
        let r := deposit env world
        isSuccessful r →
          Bank.balances (after world r) env.sender = Bank.balances (before world) env.sender + env.value ∧
          Bank.totalDeposits (after world r) = Bank.totalDeposits (before world) + env.value ∧
          emits Bank.Deposit r
    @*/

    /*@ ONCHAIN [steps: 4000] withdraw : { uint256 : asAbi } -> () @*/
    function withdraw(uint256 amount) external {
        if (paused) revert Paused();
        uint256 available = balances[msg.sender];
        if (available < amount) revert Insufficient(available);
        balances[msg.sender] = available - amount;
        totalDeposits -= amount;
        (bool ok, ) = msg.sender.call{value: amount}("");
        if (!ok) revert TransferFailed();
        emit Withdrawal(msg.sender, amount);
    }

    /*@ PROPERTY withdraw_pays_the_caller :
      ∀ (amount : Nat) (env : Env) (world : World),
        let r := withdraw amount env world
        isSuccessful r →
          canWithdraw (before world) env.sender amount ∧
          paidTo env.sender r = amount ∧
          Bank.balances (after world r) env.sender = Bank.balances (before world) env.sender - amount
    @*/

    /*@ PROPERTY withdraw_keeps_others_balances :
      ∀ (amount : Nat) (env : Env) (world : World) (a : Nat),
        let r := withdraw amount env world
        isAddress a → a ≠ env.sender →
          Bank.balances (after world r) a = Bank.balances (before world) a
    @*/

    /*@ ONCHAIN setPaused : bool -> () @*/
    function setPaused(bool p) external {
        if (msg.sender != owner) revert NotOwner();
        paused = p;
    }

    /*@ PROPERTY only_the_owner_pauses :
      ∀ (env : Env) (world : World),
        let r := dispatch env world
        Bank.paused (after world r) ≠ Bank.paused (before world) →
          env.sender = Bank.owner (before world)
    @*/

    /*@ PROPERTY owner_never_changes :
      ∀ (env : Env) (world : World),
        Bank.owner (after world (dispatch env world)) = Bank.owner (before world)
    @*/

    /*@ PROPERTY solvency_is_preserved :
      ∀ (env : Env) (world : World),
        let r := dispatch env world
        env.sender ≠ env.self →
        Bank.totalDeposits (before world) ≤ env.balance →
          Bank.totalDeposits (after world r) ≤ balanceAfter env r
    @*/
}
