# Deployed mainnet bytecode

| File | Contract | Address | Source |
| --- | --- | --- | --- |
| `WETH9.bin-runtime` | Wrapped Ether (WETH9) | `0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2` | `WETH9.sol.txt` (GPL-3.0, from <https://github.com/gnosis/canonical-weth>) |

`WETH9.bin-runtime` is the runtime bytecode returned by `eth_getCode` at Ethereum mainnet
block 26170475 (via `https://ethereum-rpc.publicnode.com`): 3124 bytes, sha256
`5566bf50796faf93c9b6f6adacd3b32c70bfe16b48ffc59db6cd144cbdc89739`. It was compiled in 2017
with solc 0.4.x, so it uses that compiler's idioms (`DIV` by `2^224` for the selector,
`EXP`-computed masks, unchecked arithmetic, no argument validation).

To fetch it again:

```bash
curl -s -X POST -H 'Content-Type: application/json' \
  --data '{"jsonrpc":"2.0","method":"eth_getCode","params":["0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2","latest"],"id":1}' \
  https://ethereum-rpc.publicnode.com
```
