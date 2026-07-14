import GRN.Basic

/-!
# The signed interaction graph

Collapses a GRN's operators to a signed, directed species-to-species
interaction graph: an edge `(src, dst, sign)` records that `src` regulates
`dst` with the given sign (`+1` activation, `-1` repression, `0` non-monotone).

Edge signs are read from operator kinetics, matching quiver's
`quiver.objective.certificate.signed_interaction_graph`. A single-input Hill or
receiver operator with `alpha = [a0, a1]` activates when `a1 > a0` and represses
when `a1 < a0`. A two-input `hill2` operator contributes a per-input sign read
from its four-entry response vector.

The sign is read from real-valued kinetics, so this extraction is the one place a
finite-precision boundary enters (`Float` comparisons do not reduce in the Lean
kernel). The downstream certificates in `GRN.Certificate` operate on the
resulting integer-signed graph and are kernel-checkable; this extraction is
evaluated by the compiler in the `analyze` executable.
-/

namespace GRN

/-- A signed edge of the species-level interaction graph:
`(source species, target species, sign ∈ {-1, 0, +1})`. -/
abbrev SignedEdge := String × String × Int

/-- Sign of a single-input Hill/receiver operator from its `[basal, max]`
expression bounds: `+1` if `max > basal`, `-1` if `max < basal`, `none`
(no edge) if equal. -/
def pairSign (basal maximum : ℚ) : Option Int :=
  if maximum > basal then some 1
  else if maximum < basal then some (-1)
  else none

/-- Monotone sign of an input, from `(low, high)` pairs of the operator's output as that input toggles
with the other held fixed: `+1` if every pair increases (`low < high`), `-1` if every pair decreases,
`some 0` if the effect changes sign (non-monotone), `none` if the input has no effect. Comparing the
entries rather than subtracting keeps this reducible in the kernel (`ℚ` subtraction normalizes via
`Nat.gcd`, which does not reduce). -/
def signFromPairs (pairs : List (ℚ × ℚ)) : Option Int :=
  let positive := pairs.any (fun p => decide (p.1 < p.2))
  let negative := pairs.any (fun p => decide (p.2 < p.1))
  if positive && negative then some 0
  else if positive then some 1
  else if negative then some (-1)
  else none

/-- Per-input-port sign of an operator's effect on the species it produces.
`none` marks a port with no effect (dropped); `some 0` a non-monotone port. -/
def operatorInputSigns (n : Node) : List (Option Int) :=
  match n.kind with
  | .receiver | .hill1 =>
      match n.alphaNums with
      | a0 :: a1 :: _ => [pairSign a0 a1]
      | _ => [none]
  | .hill2 =>
      match n.alphaNums with
      | a0 :: a1 :: a2 :: a3 :: _ =>
          -- `[a0,a1,a2,a3]` is LOICA's `a0 + a1*r1 + a2*r2 + a3*r1*r2`, `r1` the port-0 input.
          -- Each pair compares the operator's output as one input toggles with the other held fixed.
          [signFromPairs [(a0, a1), (a2, a3)], signFromPairs [(a0, a2), (a1, a3)]]
      | _ => [none, none]
  | .sum => List.replicate (max 1 n.nInputs) (some 1)
  | _ => []

/-- Edges from one operator: walk its per-port signs and input species in lockstep, emitting an edge to
every output species for each input that has a monotone effect. -/
def edgesFrom : List (Option Int) → List String → List String → List SignedEdge
  | s :: ss, src :: is, outputs =>
      (match s with
       | some sign => outputs.map (fun dst => (src, dst, sign))
       | none => []) ++ edgesFrom ss is outputs
  | _, _, _ => []

/-- The per-port signs from which an operator's edges are built. A `sum` operator adds its inputs, so every
actual input species (`g.inputsOf op.id`) carries a `+1` sign — matching the number of inputs the edge
walk consumes, rather than the declared `nInputs`. Other kinds read `operatorInputSigns`. -/
def opEdgeSigns (g : GRN) (op : Node) : List (Option Int) :=
  match op.kind with
  | .sum => List.replicate (g.inputsOf op.id).length (some 1)
  | _ => operatorInputSigns op

/-- The signed edges contributed by a list of operators. -/
def opEdges (g : GRN) : List Node → List SignedEdge
  | [] => []
  | op :: ops =>
      edgesFrom (g.opEdgeSigns op) (g.inputsOf op.id) (g.outputsOf op.id) ++ opEdges g ops

/-- Collapse operators to a signed, directed species-to-species interaction graph: one signed edge from
every input species to every species an operator produces; inputs with no effect are dropped. -/
def signedInteractionGraph (g : GRN) : List SignedEdge := opEdges g g.operators

end GRN
