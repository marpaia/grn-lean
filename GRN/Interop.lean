import Lean.Data.Json
import GRN.Certificate

/-!
# quiver ↔ grn-lean interop

Parses the JSON a quiver `GRN.to_dict` emits into a `GRN`, and emits a JSON
report: the signed interaction graph and each structural certificate. This is
the design/validation handoff — a design tool hands over a candidate network
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

/-- Read the `alpha` parameter (the sign-bearing one) from a params object.
Other parameters are threaded in when the Hill-kinetic vector field needs them. -/
def paramsFromJson (j : Json) : List (String × ParamValue) :=
  match j.getObjVal? "alpha" with
  | .ok a  => [("alpha", jsonToParam a)]
  | .error _ => []

/-- Parse one node from its JSON object. -/
def nodeFromJson (j : Json) : Except String Node := do
  let id ← j.getObjValAs? String "id"
  let kind ← parseKind (← j.getObjValAs? String "kind")
  let name := (j.getObjValAs? String "name").toOption.getD ""
  let nInputs := (j.getObjValAs? Nat "inputCount").toOption.getD 1
  let params := match j.getObjVal? "params" with
    | .ok p => paramsFromJson p
    | .error _ => []
  return { id := id, kind := kind, name := name, params := params, nInputs := nInputs }

/-- Parse one edge from its JSON object. -/
def edgeFromJson (j : Json) : Except String Edge := do
  let source ← j.getObjValAs? String "source"
  let target ← j.getObjValAs? String "target"
  let port := (j.getObjValAs? Nat "port").toOption.getD 0
  return { source := source, target := target, port := port }

/-- Parse a whole GRN from the JSON quiver emits. -/
def grnFromJson (j : Json) : Except String GRN := do
  let nodesArr ← (← j.getObjVal? "nodes").getArr?
  let edgesArr ← (← j.getObjVal? "edges").getArr?
  let nodes ← nodesArr.toList.mapM nodeFromJson
  let edges ← edgesArr.toList.mapM edgeFromJson
  return { nodes := nodes, edges := edges }

/-- The structural report: the signed interaction graph plus every certificate. -/
def report (g : GRN) : Json :=
  let edges := signedInteractionGraph g
  let sgraph := edges.map (fun e =>
    Json.arr #[Json.str e.1, Json.str e.2.1, Json.num (JsonNumber.fromInt e.2.2)])
  Json.mkObj [
    ("signedInteractionGraph", Json.arr sgraph.toArray),
    ("monotone", Json.bool (isMonotoneEdges edges)),
    ("positiveLoop", Json.bool (hasPositiveLoopEdges edges)),
    ("negativeLoop", Json.bool (hasNegativeLoopEdges edges)),
    ("certifies", Json.mkObj [
      ("sensor", Json.bool (certifiesEdges edges .sensor)),
      ("switch", Json.bool (certifiesEdges edges .switch)),
      ("oscillator", Json.bool (certifiesEdges edges .oscillator))])]

end GRN
