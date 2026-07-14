import Mathlib

/-!
# The GRN design object

A gene-regulatory network as a bipartite graph of genetic *species*
(`regulator`, `reporter`, `supplement`) and regulatory *operators*
(`source`, `receiver`, `hill1`, `hill2`, `sum`), wired by directed edges.

This mirrors quiver's `quiver.grn.GRN` field-for-field so a design serialized
by quiver round-trips into Lean (see `GRN.Interop`). It is the candidate a
design search proposes and hands here for a machine-checked structural verdict.

Kinetics are exact rationals (`ℚ`): quiver's JSON numbers are decimal literals,
so they parse without loss, and `ℚ` comparisons reduce in the Lean kernel, so
the sign of a regulatory edge, and hence every certificate, is decidable by
`decide` rather than stranded behind an opaque `Float`.

The datatypes are top-level; their operations live in the `GRN` namespace.
-/

/-- A node parameter value: a rational, a string, or a (possibly nested) list,
mirroring the JSON shapes quiver emits for `alpha`, `K`, `n`, etc. -/
inductive ParamValue where
  | num  : ℚ → ParamValue
  | str  : String → ParamValue
  | list : List ParamValue → ParamValue
  deriving Inhabited, Repr

/-- The numeric entries of a one-level list value (e.g. `alpha = [a0, a1]`),
dropping non-numeric entries. A scalar or nested value yields `[]`. -/
def ParamValue.numList : ParamValue → List ℚ
  | .list xs => xs.filterMap (fun v => match v with | .num x => some x | _ => none)
  | _ => []

/-- The eight node kinds: three species, five operators. -/
inductive NodeKind where
  | regulator | reporter | supplement | source | receiver | hill1 | hill2 | sum
  deriving DecidableEq, Repr, Inhabited

/-- Whether a kind is a regulatory operator (as opposed to a genetic species). -/
def NodeKind.isOperator : NodeKind → Bool
  | .source | .receiver | .hill1 | .hill2 | .sum => true
  | _ => false

/-- A node: its id, kind, display name, parameters, and (for `sum`) input arity. -/
structure Node where
  id : String
  kind : NodeKind
  name : String := ""
  params : List (String × ParamValue) := []
  nInputs : Nat := 1
  deriving Repr, Inhabited

/-- A directed wire from `source` to `target`; `port` selects the target
operator's input slot. -/
structure Edge where
  source : String
  target : String
  port : Nat := 0
  deriving Repr, Inhabited

/-- A gene-regulatory network: its nodes and the edges wiring them. -/
structure GRN where
  nodes : List Node := []
  edges : List Edge := []
  deriving Repr, Inhabited

namespace GRN

/-- The value of a named parameter, if present. -/
def _root_.Node.param? (n : Node) (key : String) : Option ParamValue :=
  (n.params.find? (·.1 == key)).map (·.2)

/-- The numeric `alpha` vector `[a0, a1, ...]` of a node (empty if absent). -/
def _root_.Node.alphaNums (n : Node) : List ℚ :=
  ((n.param? "alpha").map ParamValue.numList).getD []

/-- The operators (non-species nodes) of the network. -/
def operators (g : GRN) : List Node :=
  g.nodes.filter (·.kind.isOperator)

/-- The species (non-operator nodes) of the network. -/
def species (g : GRN) : List Node :=
  g.nodes.filter (fun n => !n.kind.isOperator)

/-- Insert an edge into a port-sorted list (a kernel-reducible stable sort). -/
def insertByPort (e : Edge) : List Edge → List Edge
  | [] => [e]
  | f :: fs => if e.port ≤ f.port then e :: f :: fs else f :: insertByPort e fs

/-- Sort edges by input port. -/
def sortByPort : List Edge → List Edge
  | [] => []
  | e :: es => insertByPort e (sortByPort es)

/-- The source node ids feeding an operator, ordered by input port. -/
def inputsOf (g : GRN) (opId : String) : List String :=
  (sortByPort (g.edges.filter (·.target == opId))).map (·.source)

/-- The species node ids an operator produces. -/
def outputsOf (g : GRN) (opId : String) : List String :=
  (g.edges.filter (·.source == opId)).map (·.target)

end GRN
