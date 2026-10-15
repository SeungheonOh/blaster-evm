/-!
# Reading solver values

Blaster prints counterexample values as the solver gives them: integers, `(- n)`,
constructor applications `(Evm.Msg.mk a b …)`, lists `(List.cons a (List.cons b List.nil))`
or `[a, b]`. `SExp.parse` reads them.
-/

namespace UAL

inductive SExp where
  | num (n : Int)
  | atom (s : String)
  | list (xs : List SExp)
  /-- A constructor application `(C args…)` (or a nullary constructor, with no args). -/
  | app (c : String) (args : List SExp)
deriving Inhabited, Repr, BEq

namespace SExp

def tokenize (s : String) : List String := Id.run do
  let mut toks : Array String := #[]
  let mut cur := ""
  for c in s.toList do
    if c.isWhitespace || c == ',' then
      if cur != "" then toks := toks.push cur; cur := ""
    else if c == '(' || c == ')' || c == '[' || c == ']' then
      if cur != "" then toks := toks.push cur; cur := ""
      toks := toks.push c.toString
    else cur := cur.push c
  if cur != "" then toks := toks.push cur
  return toks.toList

def atomOf (t : String) : SExp :=
  if t.all Char.isDigit && t != "" then .num t.toNat!
  else if t == "List.nil" || t == "[]" then .list []
  else if t.startsWith "Evm." || t.startsWith "UAL." then .app t []
  else .atom t

/-- Build a value from the items of a parenthesized group. -/
def build : List SExp → Except String SExp
  | [] => pure (.list [])
  | [.atom "-", .num n] => pure (.num (-n))
  | [.app "List.cons" [], h, .list t] => pure (.list (h :: t))
  | [.atom "List.cons", h, .list t] => pure (.list (h :: t))
  | [.atom "as", v, _] => pure v
  | [.app "as" [], v, _] => pure v
  | .app c [] :: args => pure (.app c args)
  | .atom c :: args => pure (.app c args)
  | _ => throw "cannot read value"

partial def parseAux : List String → Except String (SExp × List String)
  | [] => throw "unexpected end of value"
  | "(" :: rest => do
    let (items, rest) ← parseItems ")" rest []
    return (← build items, rest)
  | "[" :: rest => do
    let (items, rest) ← parseItems "]" rest []
    return (.list items, rest)
  | t :: rest => if t == ")" || t == "]" then throw s!"unexpected '{t}'" else pure (atomOf t, rest)
where
  parseItems (close : String) : List String → List SExp → Except String (List SExp × List String)
    | [], _ => throw s!"missing '{close}'"
    | t :: rest, acc =>
      if t == close then pure (acc.reverse, rest)
      else do
        let (v, rest') ← parseAux (t :: rest)
        parseItems close rest' (v :: acc)

def parse (s : String) : Except String SExp := do
  let (v, rest) ← parseAux (tokenize s)
  if !rest.isEmpty then throw "trailing input in value"
  return v

def short (c : String) : String := (c.splitOn ".").getLast!

/-- The value as a Lean term. -/
partial def toLean : SExp → String
  | .num n => if n < 0 then s!"({n})" else toString n
  | .atom a => a
  | .list xs => "[" ++ ", ".intercalate (xs.map toLean) ++ "]"
  | .app c [] => c
  | .app c args => "(" ++ c ++ " " ++ " ".intercalate (args.map toLean) ++ ")"

/-- A solver value as a Lean term (unchanged if it cannot be read). -/
def leanOfValue (s : String) : String :=
  match parse s with
  | .ok v => toLean v
  | .error _ => s

def asNat? : SExp → Option Nat
  | .num n => if n ≥ 0 then some n.toNat else none
  | _ => none

def asList? : SExp → Option (List SExp)
  | .list xs => some xs
  | _ => none

end SExp

#guard (SExp.parse "(Evm.Msg.mk 1 2 (List.cons 3 (List.cons 4 List.nil)) (- 5))" |>.toOption) ==
  some (.app "Evm.Msg.mk" [.num 1, .num 2, .list [.num 3, .num 4], .num (-5)])
#guard (SExp.parse "(Evm.Query.keccak 64 [7, 0])" |>.toOption) ==
  some (.app "Evm.Query.keccak" [.num 64, .list [.num 7, .num 0]])

end UAL
