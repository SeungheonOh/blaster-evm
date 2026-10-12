// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

/// A 2-of-3 multisignature wallet. Any owner submits a payment; owners confirm it; once
/// two owners have confirmed, anyone can execute it, exactly once.
contract MultiSig {
    error NotOwner();
    error NoSuchTransaction();
    error AlreadyExecuted();
    error AlreadyConfirmed();
    error NotConfirmed();
    error NotEnoughConfirmations();
    error TransferFailed();

    struct Transaction {
        address to;
        uint256 value;
        bool executed;
        uint256 numConfirmations;
    }

    uint256 public constant THRESHOLD = 2;

    address public owner0;  // slot 0
    address public owner1;  // slot 1
    address public owner2;  // slot 2
    uint256 public transactionCount;  // slot 3
    mapping(uint256 => Transaction) public transactions;  // slot 4: 4 slots per transaction
    mapping(uint256 => mapping(address => bool)) public isConfirmed;  // slot 5

    event Submitted(uint256 indexed id, address indexed to, uint256 value);
    event Confirmed(uint256 indexed id, address indexed owner);
    event Revoked(uint256 indexed id, address indexed owner);
    event Executed(uint256 indexed id);

    constructor(address a, address b, address c) {
        owner0 = a;
        owner1 = b;
        owner2 = c;
    }

    receive() external payable {}

    modifier onlyOwner() {
        if (msg.sender != owner0 && msg.sender != owner1 && msg.sender != owner2) revert NotOwner();
        _;
    }

    modifier pending(uint256 id) {
        if (id >= transactionCount) revert NoSuchTransaction();
        if (transactions[id].executed) revert AlreadyExecuted();
        _;
    }

    function submit(address to, uint256 value) external onlyOwner returns (uint256 id) {
        id = transactionCount;
        transactions[id] = Transaction({to: to, value: value, executed: false, numConfirmations: 0});
        transactionCount = id + 1;
        emit Submitted(id, to, value);
    }

    function confirm(uint256 id) external onlyOwner pending(id) {
        if (isConfirmed[id][msg.sender]) revert AlreadyConfirmed();
        isConfirmed[id][msg.sender] = true;
        transactions[id].numConfirmations += 1;
        emit Confirmed(id, msg.sender);
    }

    function revoke(uint256 id) external onlyOwner pending(id) {
        if (!isConfirmed[id][msg.sender]) revert NotConfirmed();
        isConfirmed[id][msg.sender] = false;
        transactions[id].numConfirmations -= 1;
        emit Revoked(id, msg.sender);
    }

    function execute(uint256 id) external pending(id) {
        Transaction storage t = transactions[id];
        if (t.numConfirmations < THRESHOLD) revert NotEnoughConfirmations();
        t.executed = true;
        (bool ok, ) = t.to.call{value: t.value}("");
        if (!ok) revert TransferFailed();
        emit Executed(id);
    }
}
