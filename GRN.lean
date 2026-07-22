import GRN.Basic
import GRN.InteractionGraph
import GRN.Certificate
import GRN.Examples

/-!
# grn-lean

Formalizing gene-regulatory circuits in the Hill-kinetic ODE perspective, and
machine-checking the structural certificates that validate a design.

The umbrella import brings in the design object, the signed interaction graph,
the structural certificates, and the worked examples. The JSON bridge lives in
`GRN.Interop` (kept out of this import so the core stays free of the
`Lean.Data.Json` dependency).
-/
