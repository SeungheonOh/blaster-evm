import Lean

/-!
# Running subprocesses under resource limits

Every heavy process (Lean with Blaster and Z3, the solver) runs in a transient systemd
unit with a memory cap, a CPU quota and low priority, like the repository's
`scripts/limits.sh`, and one at a time across the machine: they take the same lock file as
the other check scripts.
-/

namespace UAL.Driver

structure Limits where
  mem : String := "8G"
  cpu : String := "400%"
  systemd : Bool := false

def detectSystemd : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "systemd-run", args := #["--user", "--scope", "-q", "true"] }
    return out.exitCode == 0
  catch _ => return false

def lockPath : IO System.FilePath := do
  let dir := (← IO.getEnv "XDG_RUNTIME_DIR").getD "/tmp"
  return System.FilePath.mk dir / "blaster-evm-check.lock"

/-- Run `act` holding the machine-wide check lock. -/
def withCheckLock (log : String → IO Unit) (act : IO α) : IO α := do
  let h ← IO.FS.Handle.mk (← lockPath) .write
  unless ← h.tryLock do
    log "waiting for another check to finish"
    h.lock
  try act finally h.unlock

/-- Run `cmd args` under the limits, with `env` added to the environment and an optional
    standard input; at most `runtime` seconds. With systemd, the command runs in a transient
    scope: it stays in the terminal's process group (Ctrl-C stops it and its solver
    children), and the scope's limits cover all of its processes. -/
def runLimited (lim : Limits) (cmd : String) (args : Array String) (env : Array (String × String))
    (cwd : System.FilePath) (runtime : Nat) (stdin : Option String := none) :
    IO IO.Process.Output := do
  let (prog, argv) :=
    if lim.systemd then
      ("systemd-run", #["--user", "--scope", "--quiet", "--collect",
        "-p", s!"MemoryMax={lim.mem}", "-p", "MemorySwapMax=0", "-p", s!"CPUQuota={lim.cpu}",
        "-p", s!"RuntimeMaxSec={runtime}", "--", "nice", "-n", "10", cmd] ++ args)
    else ("timeout", #["--foreground", toString runtime, "nice", "-n", "10", cmd] ++ args)
  let child ← IO.Process.spawn {
    cmd := prog, args := argv, cwd := some cwd.toString,
    env := env.map (fun (k, v) => (k, some v)),
    stdin := if stdin.isSome then .piped else .null, stdout := .piped, stderr := .piped }
  let (stdinH, child) ← child.takeStdin
  if let some s := stdin then
    stdinH.putStr s
    stdinH.flush
  let errTask ← IO.asTask child.stderr.readToEnd .dedicated
  let out ← child.stdout.readToEnd
  let err ← IO.ofExcept errTask.get
  let code ← child.wait
  return { exitCode := code, stdout := out, stderr := err }

/-- Run a light command (no limits) and return its output. -/
def runQuiet (cmd : String) (args : Array String) (cwd : Option System.FilePath := none) :
    IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := cwd.map (·.toString) }

end UAL.Driver
