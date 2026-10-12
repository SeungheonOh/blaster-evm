#!/usr/bin/env python3
"""Generate the differential test corpus (tests/Tests/Differential/Cases.lean).

Every case is an artificial EVM program (and calldata). The script runs it on go-ethereum's
reference interpreter (`evm run`, geth 1.14.12) and records geth's outcome: the returned or
reverted bytes, the nonzero storage afterwards, or an exceptional halt. The Lean suite
(tests/Tests/Differential.lean) checks that the formal machine reproduces every outcome.

    GETH_EVM=/path/to/evm python3 tests/difftest/gen_cases.py

The corpus is deterministic (fixed seed), so regenerating it is reproducible.
"""
import json
import os
import random
import subprocess
import sys

EVM = os.environ.get("GETH_EVM", "evm")
OUT = os.path.join(os.path.dirname(__file__), "..", "Tests", "Differential", "Cases.lean")
U256 = 2**256

OPS = {
    "STOP": 0x00, "ADD": 0x01, "MUL": 0x02, "SUB": 0x03, "DIV": 0x04, "SDIV": 0x05,
    "MOD": 0x06, "SMOD": 0x07, "ADDMOD": 0x08, "MULMOD": 0x09, "EXP": 0x0A,
    "SIGNEXTEND": 0x0B, "LT": 0x10, "GT": 0x11, "SLT": 0x12, "SGT": 0x13, "EQ": 0x14,
    "ISZERO": 0x15, "AND": 0x16, "OR": 0x17, "XOR": 0x18, "NOT": 0x19, "BYTE": 0x1A,
    "SHL": 0x1B, "SHR": 0x1C, "SAR": 0x1D, "KECCAK256": 0x20, "ADDRESS": 0x30,
    "BALANCE": 0x31, "ORIGIN": 0x32, "CALLER": 0x33, "CALLVALUE": 0x34,
    "CALLDATALOAD": 0x35, "CALLDATASIZE": 0x36, "CALLDATACOPY": 0x37, "CODESIZE": 0x38,
    "CODECOPY": 0x39, "GASPRICE": 0x3A, "EXTCODESIZE": 0x3B, "RETURNDATASIZE": 0x3D,
    "RETURNDATACOPY": 0x3E, "EXTCODEHASH": 0x3F, "BLOCKHASH": 0x40, "COINBASE": 0x41,
    "TIMESTAMP": 0x42, "NUMBER": 0x43, "PREVRANDAO": 0x44, "GASLIMIT": 0x45,
    "CHAINID": 0x46, "SELFBALANCE": 0x47, "BASEFEE": 0x48, "BLOBHASH": 0x49,
    "BLOBBASEFEE": 0x4A, "POP": 0x50, "MLOAD": 0x51, "MSTORE": 0x52, "MSTORE8": 0x53,
    "SLOAD": 0x54, "SSTORE": 0x55, "JUMP": 0x56, "JUMPI": 0x57, "PC": 0x58, "MSIZE": 0x59,
    "JUMPDEST": 0x5B, "TLOAD": 0x5C, "TSTORE": 0x5D, "MCOPY": 0x5E, "PUSH0": 0x5F,
    "LOG0": 0xA0, "LOG1": 0xA1, "LOG2": 0xA2, "LOG3": 0xA3, "LOG4": 0xA4,
    "CALL": 0xF1, "RETURN": 0xF3, "STATICCALL": 0xFA, "REVERT": 0xFD, "INVALID": 0xFE,
}
for i in range(1, 17):
    OPS[f"DUP{i}"] = 0x7F + i
    OPS[f"SWAP{i}"] = 0x8F + i

BINOPS = ["ADD", "MUL", "SUB", "DIV", "SDIV", "MOD", "SMOD", "EXP", "SIGNEXTEND", "LT", "GT",
          "SLT", "SGT", "EQ", "AND", "OR", "XOR", "BYTE", "SHL", "SHR", "SAR"]
UNOPS = ["ISZERO", "NOT"]
TEROPS = ["ADDMOD", "MULMOD"]

INTERESTING = [0, 1, 2, 3, 7, 8, 31, 32, 255, 256, 2**128, 2**255 - 1, 2**255, 2**255 + 1,
               U256 - 2, U256 - 1, 0x8000, 0xFFFFFFFF, 0x80, 0x7F]


def push(v):
    """Shortest PUSH of v."""
    if v == 0:
        return bytes([0x5F])
    n = (v.bit_length() + 7) // 8
    return bytes([0x5F + n]) + v.to_bytes(n, "big")


def asm(*items):
    """Assemble mnemonics (str), pushes (int), raw bytes, ("label", name), ("push_label", name).

    Labels are resolved in a second pass; label pushes always use PUSH2."""
    out, labels, fixups = bytearray(), {}, []
    for it in items:
        if isinstance(it, int):
            out += push(it)
        elif isinstance(it, (bytes, bytearray)):
            out += it
        elif isinstance(it, tuple) and it[0] == "label":
            labels[it[1]] = len(out)
            out.append(OPS["JUMPDEST"])
        elif isinstance(it, tuple) and it[0] == "push_label":
            out.append(0x61)
            fixups.append((len(out), it[1]))
            out += b"\0\0"
        else:
            out.append(OPS[it])
    for pos, name in fixups:
        out[pos:pos + 2] = labels[name].to_bytes(2, "big")
    return bytes(out)


def ret_words(n):
    """Store the top `n` stack items at 0, 32, ... and return them."""
    items = []
    for i in range(n):
        items += [32 * i, "MSTORE"]
    return items + [32 * n, 0, "RETURN"]


# --------------------------------------------------------------------------------------
# Corpus


def cases():
    rnd = random.Random(20261011)
    cs = []

    def add(name, code, inp=b""):
        cs.append((name, code, inp))

    # Every binary operator on all pairs of interesting operands, one program per operator:
    # results stored at consecutive words. The first operand pushed is the second argument.
    for op in BINOPS:
        items = []
        k = 0
        for a in INTERESTING:
            for b in INTERESTING:
                items += [b, a, op, 32 * k, "MSTORE"]
                k += 1
        add(f"binop_{op.lower()}", asm(*items, 32 * k, 0, "RETURN"))
    for op in UNOPS:
        items = []
        for k, a in enumerate(INTERESTING):
            items += [a, op, 32 * k, "MSTORE"]
        add(f"unop_{op.lower()}", asm(*items, 32 * len(INTERESTING), 0, "RETURN"))
    small = [0, 1, 2, 7, 2**255, U256 - 1, U256 - 2, 2**128 + 3]
    for op in TEROPS:
        items = []
        k = 0
        for a in small:
            for b in small:
                for n in [0, 1, 7, U256 - 1, 2**200 + 9]:
                    items += [n, b, a, op, 32 * k, "MSTORE"]
                    k += 1
        add(f"terop_{op.lower()}", asm(*items, 32 * k, 0, "RETURN"))

    # Random straight-line arithmetic programs.
    pool = BINOPS + UNOPS + TEROPS
    for t in range(80):
        items, depth = [], 0
        for _ in range(rnd.randint(5, 40)):
            choice = rnd.random()
            if depth < 3 or choice < 0.35:
                v = rnd.choice(INTERESTING + [rnd.getrandbits(rnd.choice([8, 64, 160, 256]))])
                items.append(v)
                depth += 1
            elif choice < 0.45 and depth >= 2:
                n = rnd.randint(1, min(depth - 1, 16))
                items.append(f"SWAP{n}")
            elif choice < 0.55:
                n = rnd.randint(1, min(depth, 16))
                items.append(f"DUP{n}")
                depth += 1
            else:
                op = rnd.choice(pool)
                arity = 2 if op in BINOPS else 1 if op in UNOPS else 3
                if depth < arity:
                    continue
                items.append(op)
                depth += 1 - arity
        n = min(depth, 8)
        add(f"random_arith_{t}", asm(*items, *ret_words(n)))

    # Memory: random MSTORE / MSTORE8 / MLOAD / MCOPY at overlapping offsets, then return
    # the region and MSIZE.
    for t in range(40):
        items = []
        for _ in range(rnd.randint(1, 12)):
            kind = rnd.random()
            off = rnd.randint(0, 96)
            if kind < 0.45:
                items += [rnd.getrandbits(256), off, "MSTORE"]
            elif kind < 0.7:
                items += [rnd.getrandbits(8 + rnd.randint(0, 8)), off, "MSTORE8"]
            elif kind < 0.85:
                # copy an MLOAD somewhere else
                items += [off, "MLOAD", rnd.randint(0, 96), "MSTORE"]
            else:
                items += [rnd.randint(0, 40), rnd.randint(0, 96), off, "MCOPY"]
        items += ["MSIZE", 160, "MSTORE", 192, 0, "RETURN"]
        add(f"random_memory_{t}", asm(*items))

    # Calldata: loads at aligned/unaligned/out-of-range offsets, size, copies.
    for t in range(30):
        inp = bytes(rnd.getrandbits(8) for _ in range(rnd.choice([0, 1, 3, 4, 5, 31, 36, 37, 68, 100])))
        offs = [0, 1, 4, 5, 31, 32, 36, 60, 68, 99, 100, 2**64, U256 - 1]
        items = []
        k = 0
        for o in rnd.sample(offs, 6):
            items += [o, "CALLDATALOAD", 32 * k, "MSTORE"]
            k += 1
        items += ["CALLDATASIZE", 32 * k, "MSTORE"]
        k += 1
        items += [rnd.randint(0, 70), rnd.randint(0, 110), 32 * k + rnd.randint(0, 5), "CALLDATACOPY"]
        add(f"random_calldata_{t}", asm(*items, 32 * k + 96, 0, "RETURN"), inp)

    # Storage and transient storage.
    for t in range(15):
        items = []
        keys = [rnd.choice([0, 1, 2, rnd.getrandbits(256)]) for _ in range(4)]
        for _ in range(rnd.randint(1, 8)):
            k = rnd.choice(keys)
            v = rnd.choice([0, 1, rnd.getrandbits(256)])
            items += [v, k, rnd.choice(["SSTORE", "TSTORE"])]
        for i, k in enumerate(keys):
            items += [k, "SLOAD", 64 * i, "MSTORE", k, "TLOAD", 64 * i + 32, "MSTORE"]
        add(f"random_storage_{t}", asm(*items, 64 * len(keys), 0, "RETURN"))

    # keccak256 of memory regions of various lengths (rate is 136 bytes).
    for n in [0, 1, 31, 32, 33, 64, 135, 136, 137, 200]:
        items = []
        for i in range(0, 224, 32):
            items += [rnd.getrandbits(256), i, "MSTORE"]
        items += [n, rnd.randint(0, 20), "KECCAK256", 0, "MSTORE", 32, 0, "RETURN"]
        add(f"keccak_{n}", asm(*items))

    # Execution context (GAS is not modelled and excluded).
    ctx = ["ADDRESS", "ORIGIN", "CALLER", "CALLVALUE", "CALLDATASIZE", "CODESIZE", "GASPRICE",
           "COINBASE", "TIMESTAMP", "NUMBER", "PREVRANDAO", "GASLIMIT", "CHAINID",
           "SELFBALANCE", "BASEFEE", "BLOBBASEFEE", "RETURNDATASIZE", "PC", "MSIZE"]
    items = []
    for k, op in enumerate(ctx):
        items += [op, 32 * k, "MSTORE"]
    add("context", asm(*items, 32 * len(ctx), 0, "RETURN"), b"\x01\x02\x03")
    add("queries", asm(0, "BALANCE", 0, "MSTORE", "ADDRESS", "BALANCE", 32, "MSTORE",
                       "ADDRESS", "EXTCODESIZE", 64, "MSTORE", 0x1234, "EXTCODESIZE", 96, "MSTORE",
                       0, "BLOCKHASH", 128, "MSTORE", 0, "BLOBHASH", 160, "MSTORE",
                       0x1234, "EXTCODEHASH", 192, "MSTORE", 224, 0, "RETURN"))
    add("codecopy", asm(40, 3, 5, "CODECOPY", 64, 0, "RETURN"))

    # Control flow.
    add("jump_ok", asm(("push_label", "L"), "JUMP", "INVALID", ("label", "L"), 42, *ret_words(1)))
    add("jump_bad_target", asm(4, "JUMP", "STOP", "STOP", "STOP"))
    add("jump_into_push_data", asm(4, "JUMP", b"\x60\x5b", "STOP"))
    add("jumpi_taken", asm(1, ("push_label", "L"), "JUMPI", 1, *ret_words(1), ("label", "L"), 2, *ret_words(1)))
    add("jumpi_not_taken", asm(0, ("push_label", "L"), "JUMPI", 1, *ret_words(1), ("label", "L"), 2, *ret_words(1)))
    add("jumpi_not_taken_bad_target", asm(0, 3, "JUMPI", 7, *ret_words(1)))
    add("loop_sum", asm(0, 10, ("label", "L"), "DUP1", "SWAP2", "ADD", "SWAP1", 1, "SWAP1", "SUB",
                        "DUP1", ("push_label", "L"), "JUMPI", "POP", *ret_words(1)))
    add("stack_underflow", asm(1, "ADD"))
    add("stack_overflow", asm(("label", "L"), 0, ("push_label", "L"), "JUMP"))
    add("stack_1024_ok", asm(*([0] * 1024), "STOP"))
    add("invalid_opcode", asm(1, "INVALID"))
    add("undefined_opcode", asm(1, b"\x0c"))
    add("run_off_end", asm(1, 2, "ADD"))
    add("empty_code", b"")
    add("revert_data", asm(0xdeadbeef, 0, "MSTORE", 4, 28, "REVERT"))
    add("return_empty", asm(0, 0, "RETURN"))
    add("revert_after_sstore", asm(5, 1, "SSTORE", 0, 0, "REVERT"))
    add("logs", asm(7, 0, "MSTORE", 1, 2, 3, 4, 32, 0, "LOG4", 1, 1, 0, "LOG1", 9, 0, "SSTORE", "STOP"))

    # Calls to an empty account: success without return data; value without balance fails.
    add("call_empty_account", asm(0, 0, 0, 0, 0, 0xABCD, 50000, "CALL", "RETURNDATASIZE", *ret_words(2)))
    add("call_insufficient_balance", asm(0, 0, 0, 0, 1, 0xABCD, 50000, "CALL", *ret_words(1)))
    add("staticcall_empty_account", asm(32, 0, 0, 0, 0xABCD, 50000, "STATICCALL", 0, "MLOAD", *ret_words(2)))
    add("returndatacopy_out_of_bounds", asm(1, 0, 0, "RETURNDATACOPY", "STOP"))
    add("returndatacopy_empty_ok", asm(0, 0, 0, "RETURNDATACOPY", 1, *ret_words(1)))
    return cs


# --------------------------------------------------------------------------------------
# Running geth


def run_geth(code, inp):
    p = subprocess.run([EVM, "--code", code.hex(), "--input", inp.hex(), "--json", "--nomemory",
                        "--nostack", "run", "--dump"], capture_output=True, text=True)
    out = p.stdout
    summary = None
    lines = out.split("\n")
    dump_start = None
    for i, ln in enumerate(lines):
        if ln.startswith('{"output"'):
            summary = json.loads(ln)
        if ln == "{":
            dump_start = i
    if summary is None:
        raise RuntimeError(f"no summary from geth: {p.stdout[-500:]} {p.stderr[-500:]}")
    storage = []
    if dump_start is not None:
        dump = json.loads("\n".join(lines[dump_start:]))
        for acc in dump["accounts"].values():
            if acc.get("address", "").lower().endswith("7265636569766572"):
                for k, v in acc.get("storage", {}).items():
                    storage.append((int(k, 16), int(v, 16)))
    storage.sort()
    err = summary.get("error")
    ret = bytes.fromhex(summary.get("output", ""))
    if err is None:
        return ("success", ret, storage)
    if err == "execution reverted":
        return ("revert", ret, [])
    if "gas" in err:
        raise RuntimeError(f"gas-related error (gas is not modelled): {err}")
    return ("exception", err, [])


def lean_bytes(bs):
    return "0x" + bs.hex()


def main():
    rows = []
    for name, code, inp in cases():
        kind, data, storage = run_geth(code, inp)
        if kind == "success":
            st = ", ".join(f"({k}, {v})" for k, v in storage)
            exp = f'.success "{lean_bytes(data)}" [{st}]'
        elif kind == "revert":
            exp = f'.revert "{lean_bytes(data)}"'
        else:
            exp = f'.exception "{data}"'
        rows.append(f'  {{ name := "{name}", code := "{lean_bytes(code)}", input := "{lean_bytes(inp)}",\n'
                    f'    expected := {exp} }}')
    with open(OUT, "w") as f:
        f.write("import Tests.Support.Run\n\n")
        f.write("/-! Generated by `tests/difftest/gen_cases.py` from go-ethereum's `evm run` "
                "(geth 1.14.12). Do not edit. -/\n\n")
        f.write("namespace Tests.Differential\n\n")
        f.write("/-- geth's outcome: returned bytes and nonzero storage, reverted bytes, or the\n"
                "    error message of an exceptional halt. -/\n")
        f.write("inductive Expected where\n  | success (ret : String) (storage : List (Nat × Nat))\n"
                "  | revert (ret : String)\n  | exception (error : String)\n\n")
        f.write("structure Case where\n  name : String\n  code : String\n  input : String\n"
                "  expected : Expected\n\n")
        f.write("def cases : List Case := [\n" + ",\n".join(rows) + "\n]\n\n")
        f.write("end Tests.Differential\n")
    print(f"{len(rows)} cases written to {OUT}", file=sys.stderr)


if __name__ == "__main__":
    main()
