import GRN.Interop

/-!
# `analyze` — the design/validation sign-off tool

Reads a `GRN` as JSON (from a file argument or stdin) and prints its structural
report: the signed interaction graph, the bill of parts, and each certificate.
This is the executable half of the design/validation bridge.

```
lake exe analyze examples/design.json
cat examples/design.json | lake exe analyze
```

`--echo` prints the parsed design back in the input schema instead of the
report, so a sender can confirm that the design checked is the design it sent,
field for field.

```
lake exe analyze --echo examples/design.json
```
-/

open Lean GRN

def main (args : List String) : IO UInt32 := do
  let echo := args.contains "--echo"
  let paths := args.filter (fun a => !a.startsWith "--")
  let input ← match paths with
    | path :: _ => IO.FS.readFile path
    | [] => do let stdin ← IO.getStdin; stdin.readToEnd
  match Json.parse input with
  | .error e => IO.eprintln s!"parse error: {e}"; return 1
  | .ok j =>
    match grnFromJson j with
    | .error e => IO.eprintln s!"schema error: {e}"; return 1
    | .ok g =>
      IO.println (if echo then (grnToJson g).compress else (report g).compress)
      return 0
