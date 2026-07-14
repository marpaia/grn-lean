import Mathlib
import GRN.Dynamics.Interpret
import GRN.Certificate

/-!
# Tier 2 — a topological order for an acyclic GRN

An acyclic regulation relation admits a **topological order**: a rank `order : Species → ℕ` with
`regulates j i → order j < order i`. This is the enumeration the assembled-ODE Jacobian argument
(`GRN.Dynamics.Jacobian`) uses to reindex the state by `Fin n` and read off a (block-)triangular Jacobian.

Acyclicity itself is bridged from a decidable Bool check on the regulation edges (`acyclicBool`): a
concrete `GRN` value discharges `g.Acyclic` by `decide`, feeding the constructive and assembled engines
without a hand-written well-foundedness proof.
-/

namespace GRN

-- UNIT: topo-order
/-- A topological order of the regulated species of an acyclic GRN, as data: a rank in `ℕ` that strictly
increases along every regulation edge. -/
noncomputable def topoOrder (g : GRN) (h : g.Acyclic) : g.Species → ℕ := by sorry

/-- The topological order strictly increases along every regulation edge. -/
theorem topoOrder_lt (g : GRN) (h : g.Acyclic) {j i : g.Species} (hr : g.regulates j i) :
    topoOrder g h j < topoOrder g h i := by sorry

/-- The regulation edges of a GRN, every input-to-output pair carried with a placeholder `+1` sign — the
directed graph on which `acyclicBool` searches for cycles (unlike `signedInteractionGraph`, it keeps every
regulation edge, including non-monotone ones). -/
def regEdges (g : GRN) : List SignedEdge :=
  g.operators.foldr (fun op acc =>
    (g.inputsOf op.id).foldr (fun src acc2 =>
      (g.outputsOf op.id).map (fun dst => (src, dst, (1 : Int))) ++ acc2) acc) []

/-- A decidable acyclicity check: the regulation graph has no directed cycle. -/
def acyclicBool (g : GRN) : Bool := (cycleSignsEdges (regEdges g)).isEmpty

-- UNIT: acyclic-decide
/-- **Bool acyclicity ⟹ `Acyclic`.** If the Bool cycle check on the regulation edges passes, no species
transitively regulates itself, so a concrete `GRN` value discharges `g.Acyclic` by `decide`. -/
theorem acyclic_of_acyclicBool (g : GRN) (h : g.acyclicBool = true) : g.Acyclic := by sorry

end GRN
