// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// A protocol fee that the admin can only change through a timelock: a new fee is queued,
/// becomes executable `DELAY` later, and can then be applied by anyone. Users therefore
/// see every fee change coming at least `DELAY` in advance.
contract Timelock {
    error NotAdmin();
    error NothingQueued();
    error TooEarly();
    error FeeTooHigh();

    uint256 public constant DELAY = 2 days;
    uint256 public constant MAX_FEE = 1000;  // basis points

    address public admin;       // slot 0
    uint256 public fee;         // slot 1
    uint256 public pendingFee;  // slot 2
    uint256 public eta;         // slot 3: when the pending fee becomes executable, 0 if none

    event FeeQueued(uint256 newFee, uint256 eta);
    event FeeCancelled();
    event FeeChanged(uint256 oldFee, uint256 newFee);

    constructor(address admin_, uint256 fee_) {
        admin = admin_;
        fee = fee_;
    }

    function queueFee(uint256 newFee) external {
        if (msg.sender != admin) revert NotAdmin();
        if (newFee > MAX_FEE) revert FeeTooHigh();
        pendingFee = newFee;
        eta = block.timestamp + DELAY;
        emit FeeQueued(newFee, eta);
    }

    function cancel() external {
        if (msg.sender != admin) revert NotAdmin();
        pendingFee = 0;
        eta = 0;
        emit FeeCancelled();
    }

    function executeFee() external {
        if (eta == 0) revert NothingQueued();
        if (block.timestamp < eta) revert TooEarly();
        uint256 old = fee;
        fee = pendingFee;
        pendingFee = 0;
        eta = 0;
        emit FeeChanged(old, fee);
    }
}
