// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// A minimal token: balances in a mapping, minting restricted to the minter.
contract Token {
    error NotMinter();
    error InsufficientBalance();

    mapping(address => uint256) public balanceOf;  // slot 0
    uint256 public totalSupply;                     // slot 1
    address public minter;                          // slot 2

    event Transfer(address indexed from, address indexed to, uint256 value);

    function transfer(address to, uint256 amount) external returns (bool) {
        uint256 fromBalance = balanceOf[msg.sender];
        if (fromBalance < amount) revert InsufficientBalance();
        unchecked {
            balanceOf[msg.sender] = fromBalance - amount;
        }
        balanceOf[to] += amount;
        emit Transfer(msg.sender, to, amount);
        return true;
    }

    function mint(address to, uint256 amount) external {
        if (msg.sender != minter) revert NotMinter();
        totalSupply += amount;
        balanceOf[to] += amount;
        emit Transfer(address(0), to, amount);
    }
}
