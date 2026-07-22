# A Lean 4 Formalization of Gene-Regulatory Circuits in the Hill-Kinetic ODE Perspective

[![CI](https://github.com/marpaia/grn-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/marpaia/grn-lean/actions/workflows/ci.yml)
![Lean](https://img.shields.io/badge/Lean-4.31.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.31.0-blue)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)
![proofs: sorry-free](https://img.shields.io/badge/proofs-sorry--free-brightgreen)
[![built on: crnt-lean](https://img.shields.io/badge/built%20on-crnt--lean-8A2BE2)](https://github.com/marpaia/crnt-lean)

**Formal verification for [LOICA](https://github.com/RudgeLab/LOICA) circuits: machine-checked
structural certificates for the Hill-kinetic networks LOICA simulates.**

LOICA is where a genetic circuit gets built and scored. You assemble a `GeneticNetwork` from
`GeneProduct`s and Hill operators, hand it a parameter set, and integrate. That is the SPICE half of
the design loop, and it is indispensable. It is also, like SPICE, a _sampling_ argument: it tells you
what the circuit does at the parameter points you swept, and electronic design automation has never
shipped on that alone. It pairs the simulator with a formal verification tool that discharges a
property over the whole space at once.

`grn-lean` is that second tool for LOICA. It reads the same network LOICA would integrate and returns
a **kernel-checked structural certificate**: a guarantee that follows from the _wiring_ alone, and so
holds at every parameterization, including the corners an ensemble sweep never reached.

A certificate is a graph-theoretic predicate that is a proven _necessary_ condition for a target
dynamical regime, read from the topology with no simulation:

| Regime         | Certificate                                       | Result                                                                                                                          |
| -------------- | ------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| **Sensor**     | interaction-graph monotonicity (sign-consistency) | Angeli–Sontag: a monotone system has a unique, monotone steady-state response, so the dose-response and its EC50 are well posed |
| **Switch**     | a positive feedback loop                          | Thomas / Soulé / Gouzé: a positive circuit is necessary for multistationarity (bistable memory)                                 |
| **Oscillator** | a negative feedback loop                          | Thomas / Snoussi: a negative circuit is necessary for sustained oscillation                                                     |

## The design/validation handoff

A LOICA network serializes to JSON; `grn-lean` reads it and returns the signed interaction graph and
each certificate. Where LOICA hands back trajectories for one parameter set, `analyze` hands back a
verdict over all of them.

```bash
# a serialized design in, a machine-checked structural verdict out
lake exe analyze examples/design.json
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

The JSON encoding of the design object round-trips field-for-field (see `GRN.Interop`).

## The same object LOICA integrates

`GRN.Basic` mirrors LOICA's model one for one: the three `GeneProduct` roles (`regulator`, `reporter`,
`supplement`) and the five operators (`Source`, `Receiver`, `Hill1`, `Hill2`, `Sum`), wired by directed
edges whose `port` index follows LOICA's own input ordering, so a `hill2` operator's `alpha` vector is
read with the same convention `simulate.py` integrates it under.

The edge sign is LOICA's own algebra rather than a modeling choice layered on top: `Receiver` and
`Hill1` both express `e = (α₀ + α₁·r)/(1 + r)`, so the regulation is activating exactly when
`α₁ > α₀` and repressing exactly when `α₁ < α₀`, which is what `GRN.pairSign` decides.
`notes/loica-vector-field.md` transcribes the full ODE LOICA integrates, per-operator rates included,
and that transcription is the specification the Lean vector field is built against. A certificate
proved here is therefore a claim about the system LOICA actually simulates, not about a nearby
idealization of it.

## What is checked, and the one boundary

The certificates in `GRN.Certificate` operate on the integer-signed interaction graph, contain no
`Float`, and reduce in the Lean kernel: the worked circuits in `GRN.Examples` are verified with
`by decide`, i.e. by kernel-produced proof terms.

```lean
example : hasNegativeLoopEdges repressilatorEdges = true := by decide   -- a proof, not a test
example : isMonotone sensor = true := by decide                         -- and directly on the GRN
example : certifies toggle .switch = true := by decide
```

Kinetics are exact rationals (`ℚ`), so the check runs end-to-end in the kernel: the JSON decimals of a
serialized design parse to `ℚ` without loss, and the edge sign is read by _comparing_ alpha entries (`α₀ < α₁`), which
reduces in the kernel, where subtracting would not, since `ℚ` normalizes via `Nat.gcd`. The only
residual trust is that the rational parsed from a datum equals the intended measured value; that is data
provenance, not a gap in the proof.

## Layout

- `GRN.Basic`, the design object: LOICA's species (`regulator`/`reporter`/`supplement`) and operators
  (`source`/`receiver`/`hill1`/`hill2`/`sum`).
- `GRN.InteractionGraph`: the signed species-to-species graph and the edge-sign rule.
- `GRN.Certificate`: the decidable monotonicity, positive-loop, and negative-loop certificates.
- `GRN.Examples`: worked circuits (sensor, toggle, repressilator) with kernel-checked certificates.
- `GRN.Interop` / `Analyze`: the JSON bridge and the `analyze` executable.
- `GRN.Dynamics.VectorField`, the dynamical layer: the Hill-kinetic vector field over `ℝ` and the
  dynamical theorems (below). Outside the `import GRN` umbrella, so the core stays light.

## Build

```bash
lake exe cache get  # prebuilt Mathlib oleans
lake build          # library + kernel-checked examples
lake build analyze  # the design/validation executable
lake exe analyze examples/design.json
```

The package is pinned to `leanprover/lean4:v4.31.0`, on Mathlib `v4.31.0`, and depends on
[crnt-lean](https://github.com/marpaia/crnt-lean) (same pins) for the dynamical-systems substrate.
Both are fetched by `lake`, so a fresh clone builds with no further setup.

## From checked graph fact to proven dynamical guarantee

The structural certificates are kernel-checked _graph_ predicates. The dynamical layer proves the _implication_: that each
predicate entails the dynamical property for the Hill-kinetic vector field (`notes/loica-vector-field.md`).
Every result below is sorry-free.

- **Sensor: the functor, end to end.** An arbitrary acyclic, well-posed `GRN` is interpreted into a
  feedforward system whose steady state is unique and constructive (`grn_unique_steady`), nonnegative, and
  monotone in the inducer (`grn_doseResponse_mono`). Through the actual well-founded-recursion steady state
  the reporter's dose-response has a **unique EC50** (`grn_reporter_ec50`); a strict monotone path from the
  inducer to the reporter, a chain of strictly-activating regulation edges read off the graph, discharges
  the strict-monotonicity side condition, so the unique EC50 follows from the wiring alone
  (`grn_reporter_ec50_of_strictPath`, in `GRN.Dynamics.Reachability`, with a fully concrete activating
  cascade worked in `GRN.Dynamics.ReachabilityExample`). For a mixed activation/repression
  (reconvergent) circuit the balancing spin read off the monotonicity certificate gives a directional
  dose-response (`grn_reconvergent_doseResponse_of_monotone`). The analytic content (Hill monotonicity and
  strictness, cascade composition, EC50 uniqueness) is in `GRN.Dynamics.Sensor`.
- **Sensor: assembled ODE.** For the full coupled field `F x = e(x) − γ·x`, a topological enumeration read
  off the acyclic interaction graph (`topoEquiv`) makes the negated-field Jacobian triangular with positive
  diagonal, hence a P-matrix, so Gale–Nikaido gives **at most one steady state on any concentration box**
  (`grn_assembled_sensor_unique_acyclic`). The constructive and assembled steady states coincide
  (`steadyPoint_eq_equilibrium`), and the nonnegative orthant is forward-invariant
  (`nonneg_orthant_invariant`).
- **Switch.** For a monotone, sign-consistent interaction graph with no positive feedback cycle, every
  cover term of the assembled Jacobian is sign-definite, so the Jacobian is nonsingular and the equilibrium
  is locally isolated (`grn_switch_isolation`): multistationarity requires a positive cycle (Thomas /
  Soulé). The cover-sign core (`GRN.Dynamics.JacobianSigns`) reuses crnt-lean's determinant engine.
- **Oscillator: open.** The negative-cycle-for-oscillation rule is _not_ a determinant/injectivity fact
  (the repressilator has a unique equilibrium yet oscillates), so the determinant machinery does not reach
  it. It splits into two guarantees needing disjoint machinery: the _necessary-condition_ direction
  ("no negative cycle ⟹ no attracting oscillation") is monotone-cyclic-feedback theory (Mallet-Paret–Smith,
  Hirsch), absent from crnt-lean; the _realization_ direction (a negative-loop design does oscillate) is a
  Hopf bifurcation, whose spectral stack (Routh–Hurwitz, crossing gates, center-manifold reduction,
  normal-form limit cycle) does live in crnt-lean, gated on differentiable flow-dependence. Neither is
  asserted; the determinant companion (`jacobian_det_neg_of_signDefinite`) is a structural building block.

These theorems assume well-formedness of the design: `WellPosed` (positive degradation and rate
constants, alpha vectors carrying their levels) and `Node.Regular`. The switch additionally assumes
the interaction graph is monotone with a well-defined sign pattern (each edge `±1`, parallel edges
consistent).

These reuse the field-agnostic dynamical-systems substrate in
[crnt-lean](https://github.com/marpaia/crnt-lean) (LaSalle and Nagumo invariance, Gale–Nikaido /
P-matrix univalence, and the sign-definite-determinant-from-cycle-covers engine), added as a dependency
at that point. The interaction-graph and Thomas-circuit content is new: `crnt-lean` reasons about
mass-action reaction networks, whose kinetics cannot represent repression, so the Hill-kinetic view is
formalized here.

## Relationship to crnt-lean

`crnt-lean` is the mass-action reaction-network theory `grn-lean` borrows general dynamics and
fixed-point math from.

## License

Released under the MIT License. See [`LICENSE`](LICENSE).
