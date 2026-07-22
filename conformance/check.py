"""Check `analyze` against the shared certificate contract.

`cases.json` pins, for a corpus of designs, the signed interaction graph and every certificate that any
implementation of the sign rule must produce. The same corpus is checked against the Python reading in
the design tool that emits these designs, so the two readings cannot drift apart unnoticed: a change to
either one that moves a verdict fails its own repository's test.

Each case is also checked for losslessness. `analyze --echo` prints the design back in the input schema,
and the echo must carry every field of the input: dropping a node's `K`, `n`, or Component grounding on
the way in would leave the vector field in `GRN.Dynamics.Interpret` built from defaults rather than from
the design that was sent. Numeric values are compared by value, since the exact-rational parse
normalizes how a decimal is spelled (`1.0` echoes as `1`).

    python3 conformance/check.py [path-to-analyze-binary]
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent
DEFAULT_BINARY = ROOT.parent / ".lake" / "build" / "bin" / "analyze"

# The report keys that carry a verdict; the rest of the report is provenance.
VERDICT_KEYS = ("monotone", "positiveLoop", "negativeLoop")
REGIMES = ("sensor", "switch", "oscillator")


def run(binary: pathlib.Path, design: dict, *flags: str) -> dict:
    proc = subprocess.run(
        [str(binary), *flags],
        input=json.dumps(design),
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise SystemExit(f"analyze failed ({proc.returncode}): {proc.stderr.strip()}")
    return json.loads(proc.stdout)


def sorted_graph(edges) -> list:
    return sorted([list(edge) for edge in edges])


def numeric(value):
    """A parameter value compared by numeric value, so `1.0` and `1` agree."""
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return float(value)
    if isinstance(value, list):
        return [numeric(entry) for entry in value]
    return value


def node_key(node: dict) -> dict:
    return {
        "id": node["id"],
        "kind": node["kind"],
        "name": node.get("name", ""),
        "params": {k: numeric(v) for k, v in node.get("params", {}).items()},
        "inputCount": node.get("inputCount", 1),
        "componentId": node.get("componentId"),
    }


def edge_key(edge: dict) -> dict:
    return {"source": edge["source"], "target": edge["target"], "port": edge.get("port", 0)}


def check_case(binary: pathlib.Path, case: dict) -> list[str]:
    design, expected = case["design"], case["expected"]
    report = run(binary, design)
    problems: list[str] = []

    if sorted_graph(report["signedInteractionGraph"]) != sorted_graph(expected["signedInteractionGraph"]):
        problems.append(
            f"signed interaction graph: expected {sorted_graph(expected['signedInteractionGraph'])}, "
            f"got {sorted_graph(report['signedInteractionGraph'])}"
        )
    for key in VERDICT_KEYS:
        if report[key] != expected[key]:
            problems.append(f"{key}: expected {expected[key]}, got {report[key]}")
    for regime in REGIMES:
        if report["certifies"][regime] != expected["certifies"][regime]:
            problems.append(
                f"certifies.{regime}: expected {expected['certifies'][regime]}, got {report['certifies'][regime]}"
            )

    parts = sorted([n["id"], n["componentId"]] for n in design["nodes"] if n.get("componentId"))
    if sorted(report["billOfParts"]) != parts:
        problems.append(f"billOfParts: expected {parts}, got {report['billOfParts']}")

    echo = run(binary, design, "--echo")
    sent_nodes = [node_key(n) for n in design["nodes"]]
    echoed_nodes = [node_key(n) for n in echo["nodes"]]
    if echoed_nodes != sent_nodes:
        for sent, got in zip(sent_nodes, echoed_nodes):
            if sent != got:
                problems.append(f"round-trip node: sent {sent}, got {got}")
    sent_edges = [edge_key(e) for e in design["edges"]]
    echoed_edges = [edge_key(e) for e in echo["edges"]]
    if echoed_edges != sent_edges:
        problems.append(f"round-trip edges: sent {sent_edges}, got {echoed_edges}")

    return problems


def main(argv: list[str]) -> int:
    binary = pathlib.Path(argv[1]) if len(argv) > 1 else DEFAULT_BINARY
    if not binary.exists():
        raise SystemExit(f"analyze binary not found at {binary}; run `lake build analyze` first")

    cases = json.loads((ROOT / "cases.json").read_text())["cases"]
    failed = 0
    for case in cases:
        problems = check_case(binary, case)
        if problems:
            failed += 1
            print(f"FAIL {case['name']}")
            for problem in problems:
                print(f"  {problem}")
    print(f"{len(cases) - failed}/{len(cases)} conformance cases passed")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
