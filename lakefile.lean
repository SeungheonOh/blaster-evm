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

-- Properties of example contracts (see README.md). Checking them runs Blaster and Z3.
lean_lib «Examples» where
  srcDir := "."
  roots := #[`EvmBlaster.Examples.Config, `EvmBlaster.Examples.Vault,
             `EvmBlaster.Examples.VaultBuggy, `EvmBlaster.Examples.Token,
             `EvmBlaster.Examples.WETH9, `EvmBlaster.Examples.OZToken]

-- Isolated test suites on artificial programs and contracts (see tests/README.md).
@[test_driver]
lean_lib «Tests» where
  srcDir := "tests"
  roots := #[`Tests]
