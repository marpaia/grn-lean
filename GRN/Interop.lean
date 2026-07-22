import Lean.Data.Json
import GRN.Certificate

/-!
# JSON interop

Parses a serialized design into a `GRN`, and emits a JSON
report: the signed interaction graph and each structural certificate. This is
the design/validation handoff: a design tool hands over a candidate network
and gets back a kernel-checkable structural verdict, in the spirit of an EDA
formal sign-off complementing simulation.
-/

open Lean

namespace GRN

/-- A JSON decimal `mantissa · 10^(-exponent)` as an exact rational. -/
def jsonNumberToRat (n : JsonNumber) : ℚ := (n.mantissa : ℚ) / (10 : ℚ) ^ n.exponent

/-- Convert a JSON value into a `ParamValue` (numbers, strings, nested lists). -/
partial def jsonToParam (j : Json) : ParamValue :=
  match j with
  | .num n => .num (jsonNumberToRat n)
  | .str s => .str s
  | .bool b => .num (if b then 1 else 0)
  | .arr xs => .list (xs.toList.map jsonToParam)
  | .null => .list []
  | .obj _ => .list []

/-- Parse a node-kind string. -/
def parseKind : String → Except String NodeKind
  | "regulator"  => .ok .regulator
  | "reporter"   => .ok .reporter
  | "supplement" => .ok .supplement
  | "source"     => .ok .source
  | "receiver"   => .ok .receiver
  | "hill1"      => .ok .hill1
  | "hill2"      => .ok .hill2
  | "sum"        => .ok .sum
  | k            => .error s!"unknown node kind: {k}"

/-- The wire name of a node kind, the inverse of `parseKind`. -/
def kindName : NodeKind → String
  | .regulator  => "regulator"
  | .reporter   => "reporter"
  | .supplement => "supplement"
  | .source     => "source"
  | .receiver   => "receiver"
  | .hill1      => "hill1"
  | .hill2      => "hill2"
  | .sum        => "sum"

/-- Parsing a kind name is the left inverse of emitting it. -/
theorem parseKind_kindName (k : NodeKind) : parseKind (kindName k) = .ok k := by
  cases k <;> rfl

/-- Every parameter of a params object, in ascending key order.

All of a node's kinetics are carried, not just the sign-bearing `alpha`: `K`, `n`, `degradation_rate`,
`init_concentration`, `rate`, and `signal_id` are what `GRN.Dynamics.Interpret` reads to assemble the
vector field, so dropping them here would leave an imported design with a field built from defaults. -/
def paramsFromJson (j : Json) : List (String × ParamValue) :=
  match j.getObj? with
  | .ok kvs => kvs.toList.map (fun kv => (kv.1, jsonToParam kv.2))
  | .error _ => []

/-- Parse one node from its JSON object. -/
def nodeFromJson (j : Json) : Except String Node := do
  let id ← j.getObjValAs? String "id"
  let kind ← parseKind (← j.getObjValAs? String "kind")
  let name := (j.getObjValAs? String "name").toOption.getD ""
  let nInputs := (j.getObjValAs? Nat "inputCount").toOption.getD 1
  let componentId := (j.getObjValAs? String "componentId").toOption
  let params := match j.getObjVal? "params" with
    | .ok p => paramsFromJson p
    | .error _ => []
  return { id := id, kind := kind, name := name, params := params, nInputs := nInputs,
           componentId := componentId }

/-- Parse one edge from its JSON object. -/
def edgeFromJson (j : Json) : Except String Edge := do
  let source ← j.getObjValAs? String "source"
  let target ← j.getObjValAs? String "target"
  let port := (j.getObjValAs? Nat "port").toOption.getD 0
  return { source := source, target := target, port := port }

/-- Parse a whole GRN from its JSON encoding. -/
def grnFromJson (j : Json) : Except String GRN := do
  let nodesArr ← (← j.getObjVal? "nodes").getArr?
  let edgesArr ← (← j.getObjVal? "edges").getArr?
  let nodes ← nodesArr.toList.mapM nodeFromJson
  let edges ← edgesArr.toList.mapM edgeFromJson
  return { nodes := nodes, edges := edges }

/-! ## Emitting

The reverse direction, so a design round-trips: parsing then emitting reproduces the input. Losslessness
is what lets `analyze` be trusted as a checker of the design the sender actually holds, rather than of a
projection of it. -/

/-- A rational as a JSON decimal, scaling to the smallest power of ten that clears the denominator.
Every value parsed from a JSON decimal has such an expansion; a rational that does not (a denominator
with a prime factor other than 2 or 5, unreachable from parsed input) is emitted as `num/den`. -/
def ratToJson (q : ℚ) : Json :=
  match (List.range 32).findSome? (fun e =>
      let scaled := q * (10 : ℚ) ^ e
      if scaled.den == 1 then some (⟨scaled.num, e⟩ : JsonNumber) else none) with
  | some n => Json.num n
  | none => Json.str s!"{q.num}/{q.den}"

/-- Emit a parameter value in the shape it was parsed from. -/
partial def paramToJson : ParamValue → Json
  | .num q => ratToJson q
  | .str s => Json.str s
  | .list xs => Json.arr (xs.map paramToJson).toArray

/-- Emit one node, omitting `componentId` when the node is not grounded. -/
def nodeToJson (n : Node) : Json :=
  Json.mkObj ([
    ("id", Json.str n.id),
    ("kind", Json.str (kindName n.kind)),
    ("name", Json.str n.name),
    ("params", Json.mkObj (n.params.map (fun kv => (kv.1, paramToJson kv.2)))),
    ("inputCount", Json.num (JsonNumber.fromNat n.nInputs))]
    ++ (match n.componentId with
        | some c => [("componentId", Json.str c)]
        | none => []))

/-- Emit one edge. -/
def edgeToJson (e : Edge) : Json :=
  Json.mkObj [
    ("source", Json.str e.source),
    ("target", Json.str e.target),
    ("port", Json.num (JsonNumber.fromNat e.port))]

/-- Emit a whole design, in the schema `grnFromJson` reads. -/
def grnToJson (g : GRN) : Json :=
  Json.mkObj [
    ("version", Json.num (JsonNumber.fromNat 1)),
    ("nodes", Json.arr (g.nodes.map nodeToJson).toArray),
    ("edges", Json.arr (g.edges.map edgeToJson).toArray)]

/-- The structural report: the signed interaction graph plus every certificate. -/
def report (g : GRN) : Json :=
  let edges := signedInteractionGraph g
  let sgraph := edges.map (fun e =>
    Json.arr #[Json.str e.1, Json.str e.2.1, Json.num (JsonNumber.fromInt e.2.2)])
  let parts := g.billOfParts.map (fun p =>
    Json.arr #[Json.str p.1, Json.str p.2])
  Json.mkObj [
    ("signedInteractionGraph", Json.arr sgraph.toArray),
    ("billOfParts", Json.arr parts.toArray),
    ("fullyGrounded", Json.bool g.fullyGrounded),
    ("monotone", Json.bool (isMonotoneEdges edges)),
    ("positiveLoop", Json.bool (hasPositiveLoopEdges edges)),
    ("negativeLoop", Json.bool (hasNegativeLoopEdges edges)),
    ("certifies", Json.mkObj [
      ("sensor", Json.bool (certifiesEdges edges .sensor)),
      ("switch", Json.bool (certifiesEdges edges .switch)),
      ("oscillator", Json.bool (certifiesEdges edges .oscillator))])]

end GRN
