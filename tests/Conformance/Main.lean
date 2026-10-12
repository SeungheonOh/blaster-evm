import Conformance.VMTests
import Conformance.StateTests

/-!
# Conformance runner

`conformance [--verbose] PATH...` runs every JSON fixture under the given paths: legacy VM
tests (`exec` field) and blockchain-form state tests (`blocks` field, `Cancun` entries
only). It prints a summary per suite directory, the reasons for out-of-scope and
inconclusive tests, and every failure, and exits with status 1 if any test failed or a
fixture could not be read. See `docs/testing.md`.
-/

open Lean Conformance

structure Tally where
  pass : Nat := 0
  passOog : Nat := 0
  inconclusive : Nat := 0
  outOfScope : Nat := 0
  fail : Nat := 0

def Tally.add (t : Tally) : Verdict → Tally
  | .pass => { t with pass := t.pass + 1 }
  | .passOutOfGas => { t with passOog := t.passOog + 1 }
  | .inconclusive _ => { t with inconclusive := t.inconclusive + 1 }
  | .outOfScope _ => { t with outOfScope := t.outOfScope + 1 }
  | .fail _ => { t with fail := t.fail + 1 }

def Tally.plus (a b : Tally) : Tally :=
  ⟨a.pass + b.pass, a.passOog + b.passOog, a.inconclusive + b.inconclusive,
   a.outOfScope + b.outOfScope, a.fail + b.fail⟩

partial def jsonFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let entries := (← p.readDir).qsort (fun a b => a.fileName < b.fileName)
    entries.foldlM (fun acc e => return acc ++ (← jsonFiles e.path)) #[]
  else if p.extension == some "json" then return #[p]
  else return #[]

def pad (s : String) (n : Nat) : String := s ++ "".pushn ' ' (n - s.length)
def padL (s : String) (n : Nat) : String := "".pushn ' ' (n - s.length) ++ s

def row (name : String) (t : Tally) : String :=
  pad name 44 ++ padL (toString t.pass) 7 ++ padL (toString t.passOog) 9
    ++ padL (toString t.inconclusive) 14 ++ padL (toString t.outOfScope) 14
    ++ padL (toString t.fail) 7

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let roots := args.filter (· != "--verbose")
  if roots.isEmpty then
    IO.eprintln "usage: conformance [--verbose] PATH..."
    return 2
  let mut reasons : Std.HashMap String Nat := {}
  let mut failures : Array String := #[]
  let mut notes : Array String := #[]
  let mut errors := 0
  let mut total : Tally := {}
  for root in roots do
    let root := root.dropRightWhile (· == '/')
    -- suites are the directories under `root`, named by their path relative to it
    let mut suites : Array (String × Tally) := #[]
    for file in ← jsonFiles root do
      let dir := (file.parent.map (·.toString)).getD root
      let suite := if dir.length > root.length then dir.drop (root.length + 1) else "."
      let mut tally : Tally := {}
      let tests ← match Json.parse (← IO.FS.readFile file) >>= members with
        | .ok ts => pure ts
        | .error e =>
          errors := errors + 1
          failures := failures.push s!"{file}: cannot read: {e}"
          pure []
      for (name, t) in tests do
        let start ← IO.monoMsNow
        let verdict? :=
          if hasField t "exec" then some (runVMTest t)
          else if (str t "network").toOption == some "Cancun" then some (runStateTest t)
          else none
        let some verdict? := verdict? | continue
        match verdict? with
        | .error e =>
          errors := errors + 1
          failures := failures.push s!"{file} {name}: cannot run: {e}"
        | .ok v =>
          tally := tally.add v
          match v with
          | .fail why => failures := failures.push s!"{suite}/{name}: {why}"
          | .inconclusive why =>
            reasons := reasons.alter "inconclusive: reads GAS" (some <| ·.getD 0 + 1)
            if verbose then notes := notes.push s!"inconclusive {suite}/{name}: {why}"
          | .outOfScope why =>
            reasons := reasons.alter s!"out of scope: {why}" (some <| ·.getD 0 + 1)
          | .passOutOfGas =>
            if verbose then notes := notes.push s!"out of gas {suite}/{name}"
          | .pass => pure ()
        let ms := (← IO.monoMsNow) - start
        if ms > 10000 then notes := notes.push s!"slow: {suite}/{name} took {ms / 1000} s"
      suites := match suites.findIdx? (·.1 == suite) with
        | some i => suites.modify i fun (s, t) => (s, t.plus tally)
        | none => suites.push (suite, tally)
    IO.println s!"{root}"
    IO.println (pad "  suite" 44 ++ padL "pass" 7 ++ padL "pass/OOG" 9 ++ padL "inconclusive" 14
      ++ padL "out of scope" 14 ++ padL "FAIL" 7)
    for (s, t) in suites do IO.println (row s!"  {s}" t)
    let sub := suites.foldl (fun acc (_, t) => acc.plus t) {}
    IO.println (row "  subtotal" sub)
    IO.println ""
    total := total.plus sub
  IO.println (row "total" total)
  IO.println ""
  for (r, n) in reasons.toList.mergeSort (fun a b => a.2 ≥ b.2) do
    IO.println s!"{padL (toString n) 6}  {r}"
  for n in notes do IO.println n
  if !failures.isEmpty then
    IO.println s!"\n{failures.size} failures:"
    for f in failures do IO.println s!"  {f}"
  return if total.fail > 0 || errors > 0 then 1 else 0
