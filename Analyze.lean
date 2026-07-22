import GRN.Interop

/-!
# `analyze` — the design/validation sign-off tool

Reads a `GRN` as JSON (from a file argument or stdin) and prints its structural
report: the signed interaction graph and each certificate. This is the
executable half of the design/validation bridge.

```
lake exe analyze design.json
cat design.json | lake exe analyze
```
-/

open Lean GRN

def main (args : List String) : IO UInt32 := do
  let input ← match args with
    | path :: _ => IO.FS.readFile path
    | [] => do let stdin ← IO.getStdin; stdin.readToEnd
  match Json.parse input with
  | .error e => IO.eprintln s!"parse error: {e}"; return 1
  | .ok j =>
    match grnFromJson j with
    | .error e => IO.eprintln s!"schema error: {e}"; return 1
    | .ok g => IO.println (report g).compress; return 0
