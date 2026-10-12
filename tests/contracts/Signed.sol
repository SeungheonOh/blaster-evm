// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// Signed arithmetic: two's complement comparisons, sign-extension checks on `int128`
/// arguments, checked signed overflow.
contract Signed {
    function clamp(int256 x, int256 lo, int256 hi) external pure returns (int256) {
        require(lo <= hi);
        return x < lo ? lo : (x > hi ? hi : x);
    }

    function absDiff(int128 a, int128 b) external pure returns (uint256) {
        return a > b ? uint256(int256(a) - b) : uint256(int256(b) - a);
    }

    function avg(int256 a, int256 b) external pure returns (int256) {
        return (a + b) / 2;
    }
}
