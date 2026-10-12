// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

interface IERC20 {
    function transfer(address to, uint256 amount) external returns (bool);
}

/// Calls another contract and decodes its return data (the callee is answered by the world).
contract Caller {
    error TransferFailed();

    function pay(address token, address to, uint256 amount) external {
        if (!IERC20(token).transfer(to, amount)) revert TransferFailed();
    }
}
