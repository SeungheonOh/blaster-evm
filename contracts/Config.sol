// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// A parameter store guarded by a single owner.
contract Config {
    error NotOwner();
    error FeeTooHigh();
    error ZeroAddress();

    address public owner;   // slot 0
    uint256 public fee;     // slot 1
    uint256 public maxFee;  // slot 2

    event FeeChanged(uint256 oldFee, uint256 newFee);

    function setFee(uint256 newFee) external {
        if (msg.sender != owner) revert NotOwner();
        if (newFee > maxFee) revert FeeTooHigh();
        emit FeeChanged(fee, newFee);
        fee = newFee;
    }

    function transferOwnership(address newOwner) external {
        if (msg.sender != owner) revert NotOwner();
        if (newOwner == address(0)) revert ZeroAddress();
        owner = newOwner;
    }
}
