# Gene-Regulatory Circuit Design Verification in Lean 4

[![CI](https://github.com/marpaia/grn-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/marpaia/grn-lean/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.31.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.31.0-blue)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
![proofs: sorry-free](https://img.shields.io/badge/proofs-sorry--free-brightgreen)
[![built on: crnt-lean](https://img.shields.io/badge/built%20on-crnt--lean-8A2BE2)](https://github.com/marpaia/crnt-lean)

**Formalizing gene-regulatory circuits in the Hill-kinetic ODE perspective, and machine-checking the
structural certificates that validate a design.**

Electronic design automation pairs a _synthesis_ tool with a _formal verification_ tool, because
simulation only exercises the inputs you sample. Genetic circuit design has the same split. A
generator like [quiver](https://github.com/marpaia/quiver) proposes topologies and a simulator (LOICA)
scores a _sampled_ parameter ensemble — the SPICE half. `grn-lean` is the other half: a design is
handed over and gets back a **kernel-checked structural certificate**, a guarantee that holds for _every_
parameterization by the wiring alone.

A certificate is a graph-theoretic predicate that is a proven _necessary_ condition for a target
dynamical regime, read from the topology with no simulation:

| Regime         | Certificate                                       | Result                                                                                                                          |
| -------------- | ------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| **Sensor**     | interaction-graph monotonicity (sign-consistency) | Angeli–Sontag: a monotone system has a unique, monotone steady-state response, so the dose-response and its EC50 are well posed |
| **Switch**     | a positive feedback loop                          | Thomas / Soulé / Gouzé: a positive circuit is necessary for multistationarity (bistable memory)                                 |
| **Oscillator** | a negative feedback loop                          | Thomas / Snoussi: a negative circuit is necessary for sustained oscillation                                                     |

## The design/validation handoff

quiver serializes a design; `grn-lean` reads it and returns the signed interaction graph and each
certificate.

```bash
# a quiver design in, a machine-checked structural verdict out
python -c 'import json,quiver.grn as g; ...' | lake exe analyze
```

```json
{
  "signedInteractionGraph": [
    ["aTc", "TF1", 1],
    ["TF1", "GFP", -1]
  ],
  "monotone": true,
  "positiveLoop": false,
  "negativeLoop": false,
  "certifies": { "sensor": true, "switch": false, "oscillator": false }
}
```

The same design object round-trips field-for-field from quiver's `GRN.to_dict` (see `GRN.Interop`).

## What is checked, and the one boundary

The certificates in `GRN.Certificate` operate on the integer-signed interaction graph, contain no
`Float`, and reduce in the Lean kernel: the worked circuits in `GRN.Examples` are verified with
`by decide`, i.e. by kernel-produced proof terms.

```lean
example : hasNegativeLoopEdges repressilatorEdges = true := by decide   -- a proof, not a test
example : isMonotone sensor = true := by decide                         -- and directly on the GRN
example : certifies toggle .switch = true := by decide
```

Kinetics are exact rationals (`ℚ`), so the check runs end-to-end in the kernel: quiver's JSON decimals
parse to `ℚ` without loss, and the edge sign is read by _comparing_ alpha entries (`α₀ < α₁`), which
reduces in the kernel — where subtracting would not, since `ℚ` normalizes via `Nat.gcd`. The only
residual trust is that the rational parsed from a datum equals the intended measured value; that is data
provenance, not a gap in the proof.

## Layout

- `GRN.Basic` — the design object: species (`regulator`/`reporter`/`supplement`) and operators
  (`source`/`receiver`/`hill1`/`hill2`/`sum`), mirroring quiver's `quiver.grn`.
- `GRN.InteractionGraph` — the signed species-to-species graph and the edge-sign rule.
- `GRN.Certificate` — the decidable monotonicity, positive-loop, and negative-loop certificates.
- `GRN.Examples` — worked circuits (sensor, toggle, repressilator) with kernel-checked certificates.
- `GRN.Interop` / `Analyze` — the JSON bridge and the `analyze` executable.
- `GRN.Dynamics.VectorField` — the Tier-2 dynamical layer: the Hill-kinetic vector field over `ℝ` and the
  dynamical theorems (below). Outside the `import GRN` umbrella, so the core stays light.

## Build

```bash
lake exe cache get  # prebuilt Mathlib oleans
lake build          # library + kernel-checked examples
lake build analyze  # the design/validation executable
lake exe analyze design.json
```

The package is pinned to `leanprover/lean4:v4.31.0`, on Mathlib `v4.31.0`, and depends on
[crnt-lean](https://github.com/marpaia/crnt-lean) (same pins) for the Tier-2 dynamical-systems substrate.

## Tier 2: from checked graph fact to proven dynamical guarantee

The Tier-1 certificates are kernel-checked _graph_ predicates. Tier 2 proves the _implication_ — that each
predicate entails the dynamical property for the Hill-kinetic vector field (`notes/loica-vector-field.md`).
Every result below is sorry-free.

- **Sensor — the functor, end to end.** An arbitrary acyclic, well-posed `GRN` is interpreted into a
  feedforward system whose steady state is unique and constructive (`grn_unique_steady`), nonnegative, and
  monotone in the inducer (`grn_doseResponse_mono`). Through the actual well-founded-recursion steady state
  the reporter's dose-response has a **unique EC50** (`grn_reporter_ec50`); for a mixed
  activation/repression (reconvergent) circuit the balancing spin read off the monotonicity certificate
  gives a directional dose-response (`grn_reconvergent_doseResponse_of_monotone`). The analytic content —
  Hill monotonicity and strictness, cascade composition, EC50 uniqueness — is in `GRN.Dynamics.Sensor`.
- **Sensor — assembled ODE.** For the full coupled field `F x = e(x) − γ·x`, a topological enumeration read
  off the acyclic interaction graph (`topoEquiv`) makes the negated-field Jacobian triangular with positive
  diagonal, hence a P-matrix, so Gale–Nikaido gives **at most one steady state on any concentration box**
  (`grn_assembled_sensor_unique_acyclic`). The constructive and assembled steady states coincide
  (`steadyPoint_eq_equilibrium`), and the nonnegative orthant is forward-invariant
  (`nonneg_orthant_invariant`).
- **Switch.** For a monotone, sign-consistent interaction graph with no positive feedback cycle, every
  cover term of the assembled Jacobian is sign-definite, so the Jacobian is nonsingular and the equilibrium
  is locally isolated (`grn_switch_isolation`): multistationarity requires a positive cycle (Thomas /
  Soulé). The cover-sign core (`GRN.Dynamics.JacobianSigns`) reuses crnt-lean's determinant engine.
- **Oscillator — open.** The negative-cycle-for-oscillation rule is _not_ a determinant/injectivity fact
  (the repressilator has a unique equilibrium yet oscillates), so the determinant machinery does not reach
  it; it needs Hopf / monotone-cyclic-systems (Mallet-Paret–Smith, Hirsch) theory absent from crnt-lean.
  Left unasserted, with the determinant companion (`jacobian_det_neg_of_signDefinite`) as a building block.

The Tier-2 theorems assume well-formedness of the design — `WellPosed` (positive degradation and rate
constants, alpha vectors carrying their levels) and `Node.Regular` — and the switch additionally assumes
the interaction graph is monotone with a well-defined sign pattern (each edge `±1`, parallel edges
consistent).

These reuse the field-agnostic dynamical-systems substrate in
[crnt-lean](https://github.com/marpaia/crnt-lean) — LaSalle and Nagumo invariance, Gale–Nikaido /
P-matrix univalence, and the sign-definite-determinant-from-cycle-covers engine — added as a dependency
at that point. The interaction-graph and Thomas-circuit content is new: `crnt-lean` reasons about
mass-action reaction networks, whose kinetics cannot represent repression, so the Hill-kinetic view is
formalized here.

## Relationship to the neighbours

- **quiver** — the design tool. It proposes diverse topologies and scores them by simulation; `grn-lean`
  signs the delivered portfolio off. Portfolio diversity hedges the simulation proxy; a certificate
  eliminates the proxy for the property it proves.
- **crnt-lean** — the mass-action reaction-network theory `grn-lean` borrows general dynamics and
  fixed-point math from at Tier 2.

## License

Released under the MIT License. See [`LICENSE`](LICENSE).
