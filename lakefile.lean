import Lake
open Lake DSL

package «EvmBlaster» where
  moreGlobalServerArgs := #["--threads=4"]
  moreLeanArgs := #["--threads=4"]

-- Blaster is vendored as an editable local dependency (see vendor/UPSTREAMS.md).
require «Blaster» from "vendor/Lean-blaster"

@[default_target]
lean_lib «EvmBlaster» where
  roots := #[`EvmBlaster]

-- Properties of example contracts (see docs/examples.md). Checking them runs Blaster and Z3.
lean_lib «Examples» where
  srcDir := "."
  roots := #[`EvmBlaster.Examples.Config, `EvmBlaster.Examples.Vault,
             `EvmBlaster.Examples.VaultBuggy, `EvmBlaster.Examples.Token,
             `EvmBlaster.Examples.WETH9, `EvmBlaster.Examples.OZToken,
             `EvmBlaster.Examples.Timelock, `EvmBlaster.Examples.Auction,
             `EvmBlaster.Examples.MultiSig, `EvmBlaster.Examples.OZPausableToken]

-- Isolated test suites on artificial programs and contracts (see docs/testing.md).
@[test_driver]
lean_lib «Tests» where
  srcDir := "tests"
  roots := #[`Tests]

-- The UAL front end for Solidity: annotation syntax, the EVM ledger API, the `#ual_property`
-- command, and the `blaster-evm` driver (see docs/annotations.md).
lean_lib «UAL» where
  roots := #[`UAL]

lean_exe «blaster-evm» where
  root := `UAL.Driver.Main
  supportInterpreter := true

-- Conformance with the Ethereum test suites (see docs/testing.md).
lean_lib «Conformance» where
  srcDir := "tests"
  roots := #[`Conformance]

lean_exe «conformance» where
  srcDir := "tests"
  root := `Conformance.Main
