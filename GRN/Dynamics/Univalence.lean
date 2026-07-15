import Mathlib
import CRNT.Multistationarity.GaleNikaidoUniv
import CRNT.Multistationarity.JacobianDeterminantSign

/-!
# Assembled-ODE univalence: the sensor and switch bridges

This module connects the assembled multi-species vector field to crnt-lean's field-agnostic
dynamical-systems substrate, giving the two guarantees the structural certificates promise for the *full*
(reconvergent) ODE, not just the feedforward composition proved in `GRN.Dynamics.Sensor`.

* **Sensor.** `unique_equilibrium_of_pmatrix`: if the vector field's Jacobian is a P-matrix on a
  concentration box, the field is injective there (Gale–Nikaido), so there is at most one steady state.
  The dose-response has a single operating point. `isPMatrix_diagonal` discharges the P-matrix hypothesis
  in the base case (a diagonal Jacobian: degradation with no cross-regulation).
* **Switch.** `jacobian_nonsingular_of_signDefinite`: if every cycle-cover term of the Jacobian shares the
  diagonal's sign (the absence of a positive feedback cycle), the Jacobian is nonsingular, so the steady
  state is locally isolated. Multistationarity (a bistable switch) therefore *requires* a positive
  feedback cycle (Thomas / Soulé).

Both rest on `CRNT.injOn_of_pmatrix_fderiv` and `CRNT.det_ne_zero_of_coverTerm_signDefinite`; a concrete
GRN discharges the P-matrix and sign-definiteness hypotheses from its vector field and Jacobian.
-/

open CRNT
open scoped Matrix

namespace GRN.Dynamics

/-- **Sensor (Gale–Nikaido).** A vector field `F` whose Jacobian is a P-matrix at every point of a
concentration box `[lo, hi]` is injective there, so it has at most one steady state: the dose-response
has a unique operating point, for all parameterizations. -/
theorem unique_equilibrium_of_pmatrix {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))} {lo hi : Fin n → ℝ}
    (hF : ∀ z ∈ Set.Icc lo hi, HasFDerivAt F (F' z) z)
    (hP : ∀ z ∈ Set.Icc lo hi, (jacobianMatrix (F' z)).IsPMatrix)
    {a b : Fin n → ℝ} (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hFab : F a = F b) : a = b :=
  injOn_of_pmatrix_fderiv hF hP ha hb hFab

/-- A diagonal matrix with a positive diagonal is a P-matrix, the assembled sensor Jacobian's base case,
where degradation gives the (sign-flipped) diagonal and there is no cross-regulation. -/
theorem isPMatrix_diagonal {n : ℕ} {d : Fin n → ℝ} (hd : ∀ i, 0 < d i) :
    (Matrix.diagonal d).IsPMatrix := by
  intro s
  have hsub : (Matrix.diagonal d).submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))
      = Matrix.diagonal (fun i : s => d (i : Fin n)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [hsub, Matrix.det_diagonal]
  exact Finset.prod_pos (fun i _ => hd (i : Fin n))

/-- An upper-triangular matrix with positive diagonal is a P-matrix, the feedforward (acyclic) sensor
case, where a topological order makes the assembled Jacobian triangular and degradation makes its
(sign-flipped) diagonal positive. Every principal submatrix inherits triangularity, so its determinant
is the product of positive diagonal entries. -/
theorem isPMatrix_of_upperTriangular {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hUT : M.BlockTriangular id) (hpos : ∀ i, 0 < M i i) : M.IsPMatrix := by
  intro s
  have hf : StrictMono (fun i : s => (i : Fin n)) := fun _ _ h => h
  have hUT' : (M.submatrix (fun i : s => (i : Fin n)) (fun i : s => (i : Fin n))).BlockTriangular id := by
    intro i j hji
    exact hUT (hf hji)
  rw [Matrix.det_of_upperTriangular hUT']
  exact Finset.prod_pos (fun i _ => hpos _)

/-- A lower-triangular matrix with positive diagonal is a P-matrix, the orientation the assembled
Jacobian actually takes (species `i` is produced by strictly earlier species `j < i`), obtained from the
upper-triangular lemma by transposition. -/
theorem isPMatrix_of_lowerTriangular {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hLT : Mᵀ.BlockTriangular id) (hpos : ∀ i, 0 < M i i) : M.IsPMatrix := by
  have hposT : ∀ i, 0 < Mᵀ i i := fun i => by rw [Matrix.transpose_apply]; exact hpos i
  rw [← Matrix.transpose_transpose M]
  exact (isPMatrix_of_upperTriangular hLT hposT).transpose

/-- **Switch (Thomas / Soulé).** If every cycle-cover term of the Jacobian shares the diagonal term's
sign (no positive feedback cycle contributes an opposing term), the Jacobian is nonsingular. Hence a
locally isolated steady state, and multistationarity requires a positive feedback cycle. -/
theorem jacobian_nonsingular_of_signDefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ σ : Equiv.Perm (Fin n), 0 ≤ coverTerm M σ) (hdiag : 0 < coverTerm M 1) :
    M.det ≠ 0 :=
  det_ne_zero_of_coverTerm_signDefinite M (Or.inl ⟨hnn, hdiag⟩)

/-- The sign-definite-negative companion: if every cycle-cover term is nonpositive with a negative
diagonal term, the Jacobian determinant is negative. A structural building block (equilibrium index /
parity), *not* an oscillation criterion. See the oscillator note. -/
theorem jacobian_det_neg_of_signDefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hnp : ∀ σ : Equiv.Perm (Fin n), coverTerm M σ ≤ 0) (hdiag : coverTerm M 1 < 0) :
    M.det < 0 :=
  det_neg_of_coverTerm_nonpos M hnp hdiag

/-!
## Oscillator: why the determinant engine does not reach it

The oscillator certificate requires a *negative* feedback cycle (Thomas / Snoussi: necessary for
sustained oscillation). This is not a determinant/injectivity fact: the determinant-cycle-sign engine
above certifies uniqueness of equilibria (multistationarity), and oscillation is independent of
equilibrium count. The repressilator has a *unique* equilibrium yet oscillates, so no injectivity or
`det ≠ 0` argument can preclude a limit cycle.

Two independent guarantees, needing disjoint machinery, sit beyond the determinant engine:

* The *necessary-condition* direction "no negative cycle ⟹ no sustained oscillation" is the
  monotone-cyclic-feedback theory of Mallet-Paret–Smith and Hirsch (a system with no negative cycle is
  cooperative after a gauge flip, hence has no attracting periodic orbit). That order-theoretic
  machinery is absent from Mathlib and crnt-lean.
* The *realization* direction — a negative-loop design does oscillate — is spectral: a Hopf
  bifurcation, a complex-conjugate eigenvalue pair crossing the imaginary axis. That stack does live in
  crnt-lean (Routh–Hurwitz, the Hopf crossing gates, center-manifold reduction, the normal-form limit
  cycle), gated only on the differentiable dependence of the flow on its initial condition.

Neither is asserted here. The determinant companion above is a structural building block for the
equilibrium count, not a stand-in for either.
-/

end GRN.Dynamics
