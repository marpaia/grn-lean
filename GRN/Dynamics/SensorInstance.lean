import Mathlib
import GRN.Dynamics.Assembled

/-!
# Tier 2 — a concrete sensor carried end-to-end

Instantiates the assembled-ODE machinery on a concrete sensor field, validating that the pipeline
`field → hasFDerivAt → acyclic ⟹ P-matrix Jacobian ⟹ Gale–Nikaido` runs all the way to a
unique-steady-state conclusion for a real circuit.

The *general* functor — an arbitrary `GRN` value mapped to this field by interpreting its operators,
differentiating the assembled Hill kinetics, and reading a topological order off the acyclic interaction
graph — is a separate, larger construction. This file exercises the dynamical core on an explicit field.
-/

open CRNT
open scoped Matrix

namespace GRN.Dynamics

/-- A concrete minimal sensor: one reporter species produced at a constant inducer-set rate `c` and
degraded at rate `γ > 0`. Through the general `field` / `assembled_sensor_unique` machinery, its assembled
ODE `ẋ = c − γ·x` has a unique steady state on any concentration box — the dose-response has a single
operating point. -/
theorem sensor_const_unique {c γ : ℝ} (hγ : 0 < γ) {lo hi : Fin 1 → ℝ}
    {a b : Fin 1 → ℝ} (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hab : field ![γ] (fun _ => ![c]) a = field ![γ] (fun _ => ![c]) b) : a = b := by
  refine assembled_sensor_unique (E := fun _ => 0) ?_ ?_ ?_ ha hb hab
  · intro i; fin_cases i; simpa using hγ
  · intro z _; exact hasFDerivAt_const _ z
  · intro z _ i j _
    simp only [jacobianMatrix, ContinuousLinearMap.toLinearMap_zero, map_zero, Matrix.zero_apply]

end GRN.Dynamics
