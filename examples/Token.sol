// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/*@ PREDICATE
/-- A value an address can take (mapping keys are addresses). -/
def isAddress (a : Nat) : Prop := a < 2 ^ 160

/-- The balances of `a` and `b` together. -/
def holdings (s : Snapshot) (a b : Nat) : Nat := Token.balanceOf s a + Token.balanceOf s b
@*/

/// An ERC-20 token with a minting owner and infinite approvals.
contract Token {
    address public owner;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    error NotOwner();
    error InsufficientBalance(uint256 available, uint256 needed);
    error InsufficientAllowance(uint256 available, uint256 needed);
    error ZeroAddress();

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    constructor() {
        owner = msg.sender;
    }

    function _move(address from, address to, uint256 amount) internal {
        if (to == address(0)) revert ZeroAddress();
        uint256 available = balanceOf[from];
        if (available < amount) revert InsufficientBalance(available, amount);
        unchecked {
            balanceOf[from] = available - amount;
        }
        balanceOf[to] += amount;
        emit Transfer(from, to, amount);
    }

    /*@ ONCHAIN transfer : address -> uint256 -> bool @*/
    function transfer(address to, uint256 amount) external returns (bool) {
        _move(msg.sender, to, amount);
        return true;
    }

    /*@ PROPERTY transfer_moves_the_tokens :
      ∀ (to amount : Nat) (env : Env) (world : World),
        let r := transfer to amount env world
        isSuccessful r → to ≠ env.sender →
          Token.balanceOf (after world r) env.sender = Token.balanceOf (before world) env.sender - amount ∧
          Token.balanceOf (after world r) to = Token.balanceOf (before world) to + amount ∧
          emits Token.Transfer r
    @*/

    /*@ PROPERTY transfer_preserves_holdings :
      ∀ (to amount : Nat) (env : Env) (world : World),
        let r := transfer to amount env world
        holdings (after world r) env.sender to = holdings (before world) env.sender to
    @*/

    /*@ PROPERTY transfer_leaves_others_alone :
      ∀ (to amount : Nat) (env : Env) (world : World) (a : Nat),
        let r := transfer to amount env world
        isAddress a → a ≠ env.sender → a ≠ to →
          Token.balanceOf (after world r) a = Token.balanceOf (before world) a
    @*/

    /*@ PROPERTY transfer_needs_the_funds :
      ∀ (to amount : Nat) (env : Env) (world : World),
        Token.balanceOf (before world) env.sender < amount →
          isReverted (transfer to amount env world)
    @*/

    /*@ ONCHAIN approve : address -> uint256 -> bool @*/
    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        emit Approval(msg.sender, spender, amount);
        return true;
    }

    /*@ PROPERTY approve_sets_the_allowance :
      ∀ (spender amount : Nat) (env : Env) (world : World),
        let r := approve spender amount env world
        env.value = 0 →
          isSuccessful r ∧ Token.allowance (after world r) env.sender spender = amount
    @*/

    /*@ ONCHAIN [steps: 4000] transferFrom : address -> address -> uint256 -> bool @*/
    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        uint256 allowed = allowance[from][msg.sender];
        if (allowed != type(uint256).max) {
            if (allowed < amount) revert InsufficientAllowance(allowed, amount);
            unchecked {
                allowance[from][msg.sender] = allowed - amount;
            }
        }
        _move(from, to, amount);
        return true;
    }

    /*@ PROPERTY transferFrom_spends_the_allowance :
      ∀ (src to amount : Nat) (env : Env) (world : World),
        let r := transferFrom src to amount env world
        isSuccessful r →
        Token.allowance (before world) src env.sender ≠ 2 ^ 256 - 1 →
          amount ≤ Token.allowance (before world) src env.sender ∧
          Token.allowance (after world r) src env.sender = Token.allowance (before world) src env.sender - amount
    @*/

    /*@ ONCHAIN mint : address -> uint256 -> () @*/
    function mint(address to, uint256 amount) external {
        if (msg.sender != owner) revert NotOwner();
        if (to == address(0)) revert ZeroAddress();
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }

    /*@ PROPERTY only_the_owner_mints :
      ∀ (env : Env) (world : World),
        let r := dispatch env world
        Token.totalSupply (after world r) ≠ Token.totalSupply (before world) →
          env.sender = Token.owner (before world)
    @*/

    /*@ PROPERTY transfers_keep_the_supply :
      ∀ (to amount : Nat) (env : Env) (world : World),
        Token.totalSupply (after world (transfer to amount env world)) = Token.totalSupply (before world)
    @*/
}
