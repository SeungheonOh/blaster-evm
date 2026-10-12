// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// `Vault` with two bugs: `extendLock` authenticates with `tx.origin` (so any contract the
/// owner interacts with can act as the owner), and it forgets the "never shorten" check.
contract VaultBuggy {
    error NotOwner();
    error NotBeneficiary();
    error Locked();
    error TransferFailed();

    address public owner;        // slot 0
    address public beneficiary;  // slot 1
    uint256 public unlockTime;   // slot 2

    receive() external payable {}

    function withdraw(uint256 amount) external {
        if (msg.sender != beneficiary) revert NotBeneficiary();
        if (block.timestamp < unlockTime) revert Locked();
        (bool ok, ) = payable(beneficiary).call{value: amount}("");
        if (!ok) revert TransferFailed();
    }

    function extendLock(uint256 newUnlockTime) external {
        if (tx.origin != owner) revert NotOwner();
        unlockTime = newUnlockTime;
    }
}
