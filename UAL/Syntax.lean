import Lean

/-!
# UAL syntax

The annotation kinds of the
[Universal Annotation Language](https://github.com/input-output-hk/UniversalAnnotationLanguage),
as Lean syntax. The front end parses each annotation found in a Solidity file with Lean's
own parser and this grammar:

```
PREDICATE <Lean definitions>
ONCHAIN [version: Cancun] [steps: N] <function> : { <Type> : <encoding> } | <Type> -> … -> <ReturnType>
PROPERTY <name> : <statement> [:= by <tactic>]
UPLC_DATA <type>        -- recognised, but has no Solidity counterpart
```

Annotation bodies are Lean 4: the statement of a `PROPERTY` is a Lean term, the body of a
`PREDICATE` a sequence of Lean commands. In Solidity, annotations are block comments
`/*@ … @*/` (the counterpart of Plinth's `{-@ … @-}`).
-/

namespace UAL

declare_syntax_cat ual_annotation
declare_syntax_cat ual_type
declare_syntax_cat ual_option_value

syntax num : ual_option_value
syntax ident : ual_option_value

/-- `[key: value, …]`, e.g. `[version: Cancun]`, `[steps: 4000]`. -/
syntax ualOption := "[" sepBy1(ident ": " ual_option_value, ", ") "]"

/-- A Solidity type in an `ONCHAIN` signature, with its encoding: `{ uint256 : asAbi }`, or
    just `uint256` (encoded `asAbi`). `()` is the unit return type. -/
syntax ident : ual_type
syntax "(" ")" : ual_type
syntax "{ " ident " : " ident " }" : ual_type

syntax (name := predicateAnnotation) "PREDICATE" command* : ual_annotation
syntax (name := onchainAnnotation) "ONCHAIN" ualOption* ident (" : " <|> " :: ")
  sepBy1(ual_type, " -> ", (" -> " <|> " → ")) : ual_annotation
syntax (name := propertyAnnotation) "PROPERTY" ident " : " term
  (" := " "by" Lean.Parser.Tactic.tacticSeq)? : ual_annotation
syntax (name := uplcDataAnnotation) "UPLC_DATA" ident : ual_annotation

end UAL
