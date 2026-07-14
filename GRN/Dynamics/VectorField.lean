import Mathlib
import CRNT.Dynamics.Nagumo
import CRNT.Multistationarity.PMatrixUnivalence
import GRN.Certificate

/-!
# Tier 2 — the Hill-kinetic vector field

Tier 1 (`GRN.Certificate`) checks structural predicates on the signed interaction graph. Tier 2 proves
the *implication* — that a checked predicate entails the dynamical property — for the vector field LOICA
integrates (`notes/loica-vector-field.md`):

`dxₛ/dt = eₛ(x) − γₛ · xₛ`, with `e` a sum of Hill terms.

The theorems this module provides, and the crnt-lean results each reuses:

* **Sensor.** A sign-consistent interaction graph gives a Jacobian that is, after a diagonal signature, a
  P-matrix on the invariant box, hence injective — crnt-lean's Gale–Nikaido univalence
  (`CRNT.Multistationarity.PMatrixUnivalence`, `injOn_of_pmatrix_fderiv`) — so the steady state is unique
  and the dose-response monotone. This discharges the hypothesis of `GRN.certifiesEdges · .sensor`.
* **Switch.** A positive feedback loop is necessary for multistationarity, via the sign of the Jacobian
  determinant — crnt-lean's cycle-cover determinant sign (`JacobianDeterminantSign`, `DetCycleCover`).
* **Invariant box.** Production is bounded and degradation pulls inward, so the nonnegative box is forward
  invariant — `CRNT.Dynamics.Nagumo` — the compact region the dynamical claims live on.

This module is deliberately outside the `import GRN` umbrella so the Tier-1 core stays free of the heavy
analysis and crnt-lean dependencies.
-/

open Real

namespace GRN.Dynamics

/-- A single-input Hill response in LOICA's form: basal `a0` at `u = 0`, saturating to `a1` as `u → ∞`,
`(a0 + a1·(u/K)ⁿ) / (1 + (u/K)ⁿ)`. The real Hill coefficient `n` uses `Real.rpow`. -/
noncomputable def hill (a0 a1 K n u : ℝ) : ℝ :=
  (a0 + a1 * (u / K) ^ n) / (1 + (u / K) ^ n)

/-- At zero input a Hill operator sits at its basal level (for a positive Hill coefficient). This is the
`u = 0` endpoint whose comparison with the `u → ∞` level `a1` sets the edge sign in `GRN.pairSign`. -/
theorem hill_basal (a0 a1 K n : ℝ) (hn : n ≠ 0) : hill a0 a1 K n 0 = a0 := by
  unfold hill
  rw [zero_div, Real.zero_rpow hn]
  ring

end GRN.Dynamics
