// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// `require` with a reason string (ABI-encoded `Error(string)` revert data) and a string
/// return value.
contract Messages {
    function check(uint256 x) external pure returns (string memory) {
        require(x > 10, "too small");
        return "ok";
    }
}
