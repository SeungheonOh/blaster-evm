// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// Several variables packed into shared storage slots; every write is a read-modify-write
/// with masks.
contract Packed {
    address public owner;   // slot 0, bytes 0..19
    bool public paused;     // slot 0, byte 20
    uint64 public counter;  // slot 0, bytes 21..28
    uint128 public lo;      // slot 1, bytes 0..15
    uint128 public hi;      // slot 1, bytes 16..31

    function bump() external {
        require(!paused);
        counter += 1;
    }

    function setPaused(bool p) external {
        require(msg.sender == owner);
        paused = p;
    }

    function setLo(uint128 v) external { lo = v; }
    function setHi(uint128 v) external { hi = v; }
}
