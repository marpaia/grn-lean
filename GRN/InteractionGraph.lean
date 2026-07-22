import GRN.Basic

/-!
# The signed interaction graph

Collapses a GRN's operators to a signed, directed species-to-species
interaction graph: an edge `(src, dst, sign)` records that `src` regulates
`dst` with the given sign (`+1` activation, `-1` repression, `0` non-monotone).

Edge signs are read from operator kinetics. A single-input Hill or
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
actual input species (`g.inputsOf op.id`) carries a `+1` sign, matching the number of inputs the edge
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

/-! ## Grounding invariance

Which characterized part a node is grounded in is provenance, not structure: a Component fixes a node's
kinetics, and it is those kinetics the sign extraction reads. The theorems below discharge that claim
rather than asserting it, so `componentId` provably cannot move a certificate. -/

/-- The per-port signs depend on a node only through its kind, parameters, and arity. -/
theorem operatorInputSigns_congr {m n : Node} (hk : m.kind = n.kind) (hp : m.params = n.params)
    (hi : m.nInputs = n.nInputs) : operatorInputSigns m = operatorInputSigns n := by
  have ha : m.alphaNums = n.alphaNums := by simp [Node.alphaNums, Node.param?, hp]
  unfold operatorInputSigns
  rw [hk, ha, hi]

/-- Regrounding rewires nothing, so the ported inputs of every operator are untouched. -/
theorem inputsOf_regroundNodes (g : GRN) (f : String → Option String) (id : String) :
    (g.regroundNodes f).inputsOf id = g.inputsOf id := rfl

/-- Regrounding rewires nothing, so the produced species of every operator are untouched. -/
theorem outputsOf_regroundNodes (g : GRN) (f : String → Option String) (id : String) :
    (g.regroundNodes f).outputsOf id = g.outputsOf id := rfl

/-- Regrounding preserves node kinds, so it commutes with selecting the operators. -/
theorem operators_regroundNodes (g : GRN) (f : String → Option String) :
    (g.regroundNodes f).operators
      = g.operators.map (fun n => { n with componentId := f n.id }) := by
  show List.filter _ (g.nodes.map _) = List.map _ (List.filter _ g.nodes)
  induction g.nodes with
  | nil => rfl
  | cons n ns ih => by_cases h : n.kind.isOperator = true <;> simp [h, ih]

/-- An operator's per-port signs depend on it only through its id, kind, parameters, and arity, and on
the ambient network only through its wiring. -/
theorem opEdgeSigns_congr {g h : GRN} {m n : Node} (he : g.edges = h.edges) (hid : m.id = n.id)
    (hk : m.kind = n.kind) (hp : m.params = n.params) (hi : m.nInputs = n.nInputs) :
    g.opEdgeSigns m = h.opEdgeSigns n := by
  have hin : g.inputsOf m.id = h.inputsOf n.id := by simp [GRN.inputsOf, he, hid]
  have hsig : operatorInputSigns m = operatorInputSigns n := operatorInputSigns_congr hk hp hi
  unfold GRN.opEdgeSigns
  rw [hk, hin, hsig]

/-- The edges an operator contributes depend on it only through its id, kind, parameters, and arity. -/
theorem opEdges_regroundNodes (g : GRN) (f : String → Option String) :
    ∀ ops : List Node,
      opEdges (g.regroundNodes f) (ops.map (fun n => { n with componentId := f n.id }))
        = opEdges g ops
  | [] => rfl
  | op :: ops => by
      have hsigns : (g.regroundNodes f).opEdgeSigns { op with componentId := f op.id }
          = g.opEdgeSigns op := opEdgeSigns_congr rfl rfl rfl rfl rfl
      simp [opEdges, hsigns, inputsOf_regroundNodes, outputsOf_regroundNodes,
        opEdges_regroundNodes g f ops]

/-- **Grounding is provenance.** Two designs that differ only in which Components their nodes are
grounded in have the same signed interaction graph, so every certificate read from it agrees. A
structural verdict therefore transfers across a change of parts library, and a Component annotation can
never manufacture one. -/
theorem signedInteractionGraph_regroundNodes (g : GRN) (f : String → Option String) :
    signedInteractionGraph (g.regroundNodes f) = signedInteractionGraph g := by
  rw [signedInteractionGraph, operators_regroundNodes, opEdges_regroundNodes, signedInteractionGraph]

end GRN
