import GRN.InteractionGraph

/-!
# Structural certificates over the signed interaction graph

Simulation-free, parameter-independent certificates read from the topology
alone. Each is a graph-theoretic predicate that is a proven *necessary*
condition for a target dynamical regime:

- **Monotonicity** (Angeli–Sontag): a sign-consistent (balanced) interaction
  graph implies a monotone system, whose steady-state input/output response is
  unique and monotone — so for a sensor the half-maximal crossing (EC50) is
  well defined.
- **Thomas' rule** (Soulé; Gouzé; Snoussi): a positive feedback loop is
  necessary for multistationarity (a bistable, two-state switch); a negative
  loop is necessary for sustained oscillation.

These operate on the integer-signed graph (`List SignedEdge`), so they contain
no `Float` and reduce in the Lean kernel: the `_root_.GRN` examples in
`GRN.Examples` are checked with `by decide`, i.e. by kernel-produced proof
terms. The `GRN`-level wrappers compose these with `signedInteractionGraph`,
whose sign extraction crosses the finite-precision boundary and is meant for
compiled evaluation (`#eval`, the `analyze` executable), not `decide`.
-/

namespace GRN

/-- The distinct vertices appearing in a signed graph, in first-occurrence order. -/
def verticesOf (edges : List SignedEdge) : List String :=
  (edges.foldr (fun e acc => e.1 :: e.2.1 :: acc) []).foldr
    (fun x acc => if acc.any (· == x) then acc else x :: acc) []

/-- The current spin (`±1`) assigned to a vertex, if any. -/
def spinOf (spin : List (String × Int)) (v : String) : Option Int :=
  (spin.find? (·.1 == v)).map (·.2)

/-- One relaxation pass: propagate spins across every edge (treated
undirected). Returns `none` on a sign-consistency contradiction, else the
updated assignment paired with whether any new vertex was assigned. -/
def relaxPass (edges : List SignedEdge) (spin : List (String × Int)) :
    Option (List (String × Int) × Bool) :=
  edges.foldl (fun st e =>
    match st with
    | none => none
    | some (sp, changed) =>
      let a := e.1; let b := e.2.1; let s := e.2.2
      match spinOf sp a, spinOf sp b with
      | some va, some vb => if vb == s * va then some (sp, changed) else none
      | some va, none => some ((b, s * va) :: sp, true)
      | none, some vb => some ((a, s * vb) :: sp, true)
      | none, none => some (sp, changed))
    (some (spin, false))

/-- Relax to a fixed point (or a contradiction). Terminates: every productive
pass assigns at least one new vertex, and there are finitely many. -/
def relaxToFix (edges : List SignedEdge) : List (String × Int) →
    Option (List (String × Int)) :=
  let rec loop (fuel : Nat) (sp : List (String × Int)) :
      Option (List (String × Int)) :=
    match fuel with
    | 0 => some sp
    | fuel + 1 =>
      match relaxPass edges sp with
      | none => none
      | some (sp', true) => loop fuel sp'
      | some (sp', false) => some sp'
  loop (edges.length + 1)

/-- Whether the signed graph is sign-consistent: a `±1` spin can be assigned to
every vertex so that each edge's sign is the product of its endpoints' spins.
Seeds one vertex per connected component with spin `+1` and relaxes. -/
def colorable (edges : List SignedEdge) (verts : List String) : Bool :=
  let rec go (fuel : Nat) (spin : List (String × Int)) : Bool :=
    match fuel with
    | 0 => true
    | fuel + 1 =>
      match relaxToFix edges spin with
      | none => false
      | some sp =>
        match verts.find? (fun v => (spinOf sp v).isNone) with
        | none => true
        | some v => go fuel ((v, 1) :: sp)
  go (verts.length + 1) []

/-- The Angeli–Sontag monotonicity certificate on a signed graph: sign-consistent
(balanced), with no non-monotone (`0`-sign) edge. -/
def isMonotoneEdges (edges : List SignedEdge) : Bool :=
  if edges.any (fun e => e.2.2 == 0) then false
  else colorable edges (verticesOf edges)

/-- The signed out-neighbours of a vertex in the directed graph. -/
def neighbors (edges : List SignedEdge) (u : String) : List (String × Int) :=
  edges.filterMap (fun e => if e.1 == u then some (e.2.1, e.2.2) else none)

/-- The sign product of every directed simple cycle. Duplicates (a cycle found
from more than one start vertex) are harmless: only the existence of a positive
or negative product is consumed. A cycle through a non-monotone (`0`-sign) edge
has product `0`. -/
def cycleSignsEdges (edges : List SignedEdge) : List Int :=
  let verts := verticesOf edges
  let rec dfs (fuel : Nat) (start node : String) (path : List String)
      (prod : Int) : List Int :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      (neighbors edges node).foldr (fun nb acc =>
        if nb.1 == start then (prod * nb.2) :: acc
        else if path.any (· == nb.1) then acc
        else dfs fuel start nb.1 (nb.1 :: path) (prod * nb.2) ++ acc) []
  verts.foldr (fun v acc => dfs (verts.length + 1) v v [v] 1 ++ acc) []

/-- A positive feedback loop is present (necessary for multistationarity). -/
def hasPositiveLoopEdges (edges : List SignedEdge) : Bool :=
  (cycleSignsEdges edges).any (fun s => decide (0 < s))

/-- A negative feedback loop is present (necessary for sustained oscillation). -/
def hasNegativeLoopEdges (edges : List SignedEdge) : Bool :=
  (cycleSignsEdges edges).any (fun s => decide (s < 0))

/-- A target dynamical regime a design is meant to realize. -/
inductive Regime where
  | sensor | switch | oscillator
  deriving DecidableEq, Repr, Inhabited

/-- Whether a signed graph carries the necessary-condition certificate for a
regime: `sensor` needs monotonicity; `switch` a positive loop; `oscillator` a
negative loop. -/
def certifiesEdges (edges : List SignedEdge) : Regime → Bool
  | .sensor => isMonotoneEdges edges
  | .switch => hasPositiveLoopEdges edges
  | .oscillator => hasNegativeLoopEdges edges

/-! ### `GRN`-level wrappers

These read edge signs from real-valued kinetics via `signedInteractionGraph`,
so they are for compiled evaluation, not `decide`. -/

/-- Interaction-graph monotonicity of a GRN (the sensor certificate). -/
def isMonotone (g : GRN) : Bool := isMonotoneEdges (signedInteractionGraph g)

/-- Whether a GRN has a positive feedback loop (the switch certificate). -/
def hasPositiveLoop (g : GRN) : Bool := hasPositiveLoopEdges (signedInteractionGraph g)

/-- Whether a GRN has a negative feedback loop (the oscillator certificate). -/
def hasNegativeLoop (g : GRN) : Bool := hasNegativeLoopEdges (signedInteractionGraph g)

/-- Whether a GRN carries the necessary-condition certificate for a regime. -/
def certifies (g : GRN) (r : Regime) : Bool := certifiesEdges (signedInteractionGraph g) r

end GRN
