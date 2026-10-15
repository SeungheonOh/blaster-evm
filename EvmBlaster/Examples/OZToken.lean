import EvmBlaster
import Blaster

/-!
# An OpenZeppelin token

`contracts/OZToken.sol` is the OpenZeppelin Contracts Wizard output for an ERC20 with
owner-restricted minting: all of its logic is OpenZeppelin v5.1.0 (`ERC20`, `Ownable`).

Storage: `_balances` (mapping, slot 0), `_allowances` (nested mapping, slot 1),
`_totalSupply` (slot 2), `_name` (3), `_symbol` (4), `_owner` (5).

Chain-state assumptions, beyond the hashes involved being collision free (`Hashes`):
* `Deployed`: the name and symbol slots hold what the constructor stored;
* `SupplyBacked`: any two balances add up to at most the total supply. It follows from the
  ERC20 invariant "the balances sum to the total supply", which OpenZeppelin relies on to
  skip the overflow check when crediting a recipient.
-/

namespace Examples.OZToken
open Evm

#evm_contract_file OZToken "contracts/build/OZToken.bin-runtime"

def supplySlot : Nat := 2
def ownerSlot : Nat := 5

/-- "Blaster Token" and "BLT" as short storage strings. -/
def nameWord : Nat := 0x426c617374657220546f6b656e0000000000000000000000000000000000001a
def symbolWord : Nat := 0x424c540000000000000000000000000000000000000000000000000000000006

example : Solidity.shortString "Blaster Token" = nameWord := by decide
example : Solidity.shortString "BLT" = symbolWord := by decide

def Deployed (world : Query → Nat) : Prop :=
  World.storage world 3 = nameWord ∧ World.storage world 4 = symbolWord

def owner (world : Query → Nat) : Nat := World.storage world ownerSlot % U160
def supply (world : Query → Nat) : Nat := World.storage world supplySlot

/-- `_balances[a]`, before and after. -/
def bal (world : Query → Nat) (a : Nat) : Nat := World.storage world (Solidity.mappingSlot world 0 a)
def bal' (world : Query → Nat) (f : Frame) (a : Nat) : Nat :=
  f.sload world (Solidity.mappingSlot world 0 a)

/-- `_allowances[o][s]`, before and after. -/
def allowSlot (world : Query → Nat) (o s : Nat) : Nat := Solidity.mappingSlot2 world 1 o s
def allow (world : Query → Nat) (o s : Nat) : Nat := World.storage world (allowSlot world o s)
def allow' (world : Query → Nat) (f : Frame) (o s : Nat) : Nat := f.sload world (allowSlot world o s)

def SupplyBacked (world : Query → Nat) : Prop :=
  ∀ a b, a ≠ b → bal world a + bal world b ≤ supply world

def Assumptions (world : Query → Nat) : Prop :=
  World.WF world ∧ World.KeccakAbove world 6 ∧ Deployed world

/-- The hashes of the call and `extra` (the mapping entries a statement reads) do not
    collide. -/
abbrev Hashes (env : Env) (world : Query → Nat) (extra : List HashInput) : Prop :=
  HashesFree OZToken env world 5000 1 extra

/-- Only the owner changes the total supply. -/
theorem supply_changes_only_by_owner (env : Env) (world : Query → Nat) :
    env.WF → Assumptions world → Hashes env world [] →
    (execute OZToken env world 5000).onSuccess (fun f =>
      f.sload world supplySlot ≠ supply world → env.msg.caller = owner world) := by
  blaster

/-- Only the owner changes the owner. -/
theorem owner_changes_only_by_owner (env : Env) (world : Query → Nat) :
    env.WF → Assumptions world → Hashes env world [] →
    (execute OZToken env world 5000).onSuccess (fun f =>
      f.sload world ownerSlot % U160 ≠ owner world → env.msg.caller = owner world) := by
  blaster

/-- Once ownership is renounced, the supply is fixed forever (no caller is address zero). -/
theorem renounced_supply_fixed (env : Env) (world : Query → Nat) :
    env.WF → Assumptions world → Hashes env world [] → owner world = 0 → env.msg.caller ≠ 0 →
    (execute OZToken env world 5000).onSuccess (fun f =>
      f.sload world supplySlot = supply world ∧ f.sload world ownerSlot % U160 = 0) := by
  blaster

/-- Nobody can take tokens from `a` except `a`, or a spender within its allowance, which is
    then consumed (unless it is the infinite allowance). -/
theorem only_holder_or_spender_debits (env : Env) (world : Query → Nat) (a : Nat) :
    env.WF → Assumptions world → SupplyBacked world → a < U160 →
    Hashes env world (mapKey 0 a :: mapKey2 world 1 a env.msg.caller) →
    (execute OZToken env world 5000).onSuccess (fun f =>
      bal' world f a < bal world a →
        env.msg.caller = a ∨
        (bal world a - bal' world f a ≤ allow world a env.msg.caller ∧
         (allow world a env.msg.caller = U256 - 1 ∨
          allow' world f a env.msg.caller =
            allow world a env.msg.caller - (bal world a - bal' world f a)))) := by
  blaster

/-- `transfer(to, amount)` moves exactly `amount` and touches no other balance; it fails
    when the caller lacks the funds. -/
theorem transfer (env : Env) (world : Query → Nat) (to amount a : Nat) :
    env.WF → Assumptions world → SupplyBacked world →
    env.msg.calldata = .ofAbi 0xa9059cbb [to, amount] → env.msg.caller ≠ to →
    Hashes env world [mapKey 0 env.msg.caller, mapKey 0 to, mapKey 0 a] →
    (execute OZToken env world 5000).onSuccess (fun f =>
      amount ≤ bal world env.msg.caller ∧
      bal' world f env.msg.caller = bal world env.msg.caller - amount ∧
      bal' world f to = bal world to + amount ∧
      f.sload world supplySlot = supply world ∧
      (a < U160 → a ≠ env.msg.caller → a ≠ to → bal' world f a = bal world a)) := by
  blaster

/-- `approve(spender, v)` sets the caller's allowance for `spender` and nothing else. -/
theorem approve (env : Env) (world : Query → Nat) (spender v o s : Nat) :
    env.WF → Assumptions world →
    env.msg.calldata = .ofAbi 0x095ea7b3 [spender, v] →
    Hashes env world (mapKey2 world 1 env.msg.caller spender ++ mapKey2 world 1 o s) →
    (execute OZToken env world 5000).onSuccess (fun f =>
      allow' world f env.msg.caller spender = v ∧
      (o < U160 → s < U160 → (o ≠ env.msg.caller ∨ s ≠ spender) →
        allow' world f o s = allow world o s)) := by
  blaster

/-! ### The assumptions are consistent -/

#blaster (solve-result: 1) [∀ (env : Env) (world : Query → Nat) (to amount a : Nat),
    env.WF → Assumptions world → SupplyBacked world →
    env.msg.calldata = .ofAbi 0xa9059cbb [to, amount] → env.msg.caller ≠ to →
    Hashes env world [mapKey 0 env.msg.caller, mapKey 0 to, mapKey 0 a] → False]

end Examples.OZToken
