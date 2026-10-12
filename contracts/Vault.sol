// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// Holds Ether for a beneficiary. Funds are released to the beneficiary only, and only
/// after `unlockTime`, which the owner may postpone but never bring forward.
contract Vault {
    error NotOwner();
    error NotBeneficiary();
    error Locked();
    error CannotShorten();
    error TransferFailed();

    address public owner;        // slot 0
    address public beneficiary;  // slot 1
    uint256 public unlockTime;   // slot 2

    event Withdrawn(address indexed to, uint256 amount);

    receive() external payable {}

    function withdraw(uint256 amount) external {
        if (msg.sender != beneficiary) revert NotBeneficiary();
        if (block.timestamp < unlockTime) revert Locked();
        (bool ok, ) = payable(beneficiary).call{value: amount}("");
        if (!ok) revert TransferFailed();
        emit Withdrawn(msg.sender, amount);
    }

    function extendLock(uint256 newUnlockTime) external {
        if (msg.sender != owner) revert NotOwner();
        if (newUnlockTime < unlockTime) revert CannotShorten();
        unlockTime = newUnlockTime;
    }
}
