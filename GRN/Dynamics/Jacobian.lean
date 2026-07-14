import Mathlib
import GRN.Dynamics.Assembled
import GRN.Dynamics.GRNEc50
import GRN.Dynamics.TopoOrder

/-!
# Tier 2 — the assembled GRN Jacobian

The assembled ODE reindexes the regulated species by `Fin n` through an enumeration `e : Fin n ≃ Species`.
`assembledProd` is the interpreted production in that enumeration; `negJac` is the Jacobian of the negated
field `-F = γ·x − e(x)`, whose diagonal carries the positive degradation rates.

This module supplies the analytic objects the univalence bridge consumes:

* **`prodOf-fderiv`** — the assembled Hill production is Fréchet-differentiable at a strictly positive
  state (differentiating `valuation` / `opRate` / `hill` / `hill2` / `sum`), giving the field derivative.
* **`jacobian-triangular`** — under a topological enumeration (`GRN.Dynamics.TopoOrder`), `negJac` is
  block-triangular with a strictly positive (degradation) diagonal.
* **`grn-assembled-sensor-unique`** — feeding that triangular Jacobian through
  `isPMatrix_of_lowerTriangular` and `unique_equilibrium_of_pmatrix`: any acyclic, well-posed GRN has at
  most one steady state on a concentration box.
-/

namespace GRN

open Dynamics CRNT
open scoped Matrix

/-- The interpreted production reindexed by an enumeration `e : Fin n ≃ Species` — the assembled-ODE
production as a self-map of `Fin n → ℝ`. -/
noncomputable def assembledProd (g : GRN) (wp : g.WellPosed) {n : ℕ} (e : Fin n ≃ g.Species) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x k => g.prodOf wp.inducer (e k) (fun j => x (e.symm j))

/-- The Jacobian of the negated field `-F = γ·x − e(x)` from a production derivative `E`: degradation on
the diagonal minus the production Jacobian. -/
noncomputable def negJac (g : GRN) (wp : g.WellPosed) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  jacobianMatrix (Dynamics.degCLM (fun k => wp.γ (e k)) - E)

-- UNIT: prodOf-fderiv
/-- **The assembled Hill production is Fréchet-differentiable** at a strictly positive state: differentiate
`valuation` / `opRate` / `hill` / `hill2` / `sum`, giving the assembled field derivative `F'`. -/
theorem hasFDerivAt_assembledProd (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (z : Fin n → ℝ) (hz : ∀ k, 0 < z k) :
    ∃ E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), HasFDerivAt (g.assembledProd wp e) E z := by sorry

-- UNIT: jacobian-triangular
/-- **The assembled Jacobian is triangular.** Under a topological enumeration (`regulates (e k) (e l) →
k < l`), the negated-field Jacobian `negJac` is block-triangular for the identity order, with a strictly
positive (degradation) diagonal. -/
theorem negJac_blockTriangular (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (htopo : ∀ k l : Fin n, g.regulates (e k) (e l) → k < l)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) :
    (g.negJac wp e E).transpose.BlockTriangular id ∧ ∀ k, 0 < g.negJac wp e E k k := by sorry

-- UNIT: grn-assembled-sensor-unique
/-- **The assembled sensor has a unique equilibrium.** Feeding the triangular Jacobian through
`isPMatrix_of_lowerTriangular` and `unique_equilibrium_of_pmatrix`: for an acyclic, well-posed GRN with a
topological enumeration, the assembled field has at most one steady state on any concentration box. -/
theorem grn_assembled_sensor_unique (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (htopo : ∀ k l : Fin n, g.regulates (e k) (e l) → k < l) (lo hi : Fin n → ℝ)
    {a b : Fin n → ℝ} (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hab : Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) a
         = Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) b) :
    a = b := by sorry

end GRN
