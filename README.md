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
- `GRN.Dynamics.VectorField` — the Tier-2 frontier: the Hill-kinetic vector field over `ℝ` and the
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

## Roadmap: from checked graph fact to proven dynamical guarantee

Today's Tier-1 certificates are kernel-checked _graph_ predicates. Tier 2 proves the _implication_ — that
the predicate entails the dynamical property for the Hill-kinetic vector field (`notes/loica-vector-field.md`).

- **Sensor — proved (`GRN.Dynamics.Sensor`).** For the feedforward sensor topology the analytic content of
  the Angeli–Sontag guarantee is a theorem: a Hill operator's response is monotone with direction set by
  its edge sign (`hill_monotoneOn` / `hill_antitoneOn`), strictly so for a genuine activator
  (`hill_strictMonoOn`); a cascade of activating stages composes to a monotone dose-response
  (`cascade_monotoneOn`); and a strictly monotone response meets any level at exactly one input, so the
  EC50 is well defined (`ec50_unique`, `hill_ec50_unique`). Sorry-free.
- **Sensor — assembled ODE (`GRN.Dynamics.{Assembled,Univalence}`).** The field `F x = e(x) − γ·x` is
  assembled over `Fin n → ℝ` (`field`, `hasFDerivAt_field`), and `assembled_sensor_unique` proves it has
  **at most one steady state on any concentration box** for a feedforward (acyclic) production: the
  negated field's Jacobian is `diagonal γ − Jₑ`, which acyclicity makes triangular with positive diagonal
  (`isPMatrix_of_lowerTriangular`), hence a P-matrix, hence Gale–Nikaido (`unique_equilibrium_of_pmatrix`
  on crnt-lean's `injOn_of_pmatrix_fderiv`) gives injectivity. Sorry-free.
- **Forward-invariant orthant (`GRN.Dynamics.Assembled`).** `nonneg_orthant_invariant`: with nonnegative
  production, any solution starting with all species ≥ 0 stays ≥ 0 forever — proved per coordinate from
  crnt-lean's scalar Nagumo lemma. Sorry-free.
- **Switch (`GRN.Dynamics.Univalence`).** `jacobian_nonsingular_of_signDefinite`: if every Jacobian
  cycle-cover term shares the diagonal's sign — no positive feedback cycle — the Jacobian is nonsingular,
  so the equilibrium is locally isolated; multistationarity requires a positive cycle (Thomas / Soulé,
  on crnt-lean's `det_ne_zero_of_coverTerm_signDefinite`). Sorry-free.
- **Oscillator — spectral frontier (not asserted).** The negative-cycle-for-oscillation rule is _not_ a
  determinant/injectivity fact (the repressilator has a unique equilibrium yet oscillates), so no bridge
  here proves it; it needs Hopf / monotone-cyclic-systems (Mallet-Paret–Smith, Hirsch) machinery absent
  from crnt-lean. Documented honestly in `Univalence.lean` with the provable determinant companion
  (`jacobian_det_neg_of_signDefinite`) as a building block.
- **End-to-end instance (`GRN.Dynamics.SensorInstance`).** `sensor_const_unique` carries a concrete
  sensor field (`ẋ = c − γ·x`) through `field` → `assembled_sensor_unique` to a unique steady state,
  validating that the machinery instantiates from an explicit circuit. Sorry-free.
- **Remaining engineering.** The general _functor_ from an arbitrary `GRN` value: interpret its operators
  into the production `e`, differentiate the assembled Hill kinetics for the `HasFDerivAt` witnesses, and
  read a topological order off the acyclic interaction graph to supply triangularity — so any acyclic
  sensor GRN discharges `assembled_sensor_unique`'s hypotheses automatically. And the general reconvergent
  (non-triangular) sensor via monotone-systems theory.

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
