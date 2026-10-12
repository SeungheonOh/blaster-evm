// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// A fixed-length loop writing a fixed-size storage array.
contract Loop {
    uint256[4] public table;  // slots 0..3

    function fill(uint256 x) external {
        for (uint256 i = 0; i < 4; ++i) {
            table[i] = x * i;
        }
    }
}
