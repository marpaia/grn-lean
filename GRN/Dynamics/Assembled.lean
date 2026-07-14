import Mathlib
import GRN.Dynamics.Univalence
import CRNT.Dynamics.Nagumo

/-!
# The assembled gene-regulatory vector field

The species-indexed assembled field `F x = e(x) − (γ+μ)·x`: production `e` minus first-order
degradation/dilution `γ` (LOICA's `dxₛ/dt = eₛ(x) − (γₛ+μ)xₛ`). Here the state is `Fin n → ℝ`, one
coordinate per regulated species. This file supplies the analytic objects the univalence bridges in
`GRN.Dynamics.Univalence` consume: the field, its Fréchet derivative, and (under a feedforward/acyclic
hypothesis) the P-matrix Jacobian that yields a unique steady state.
-/

open CRNT

namespace GRN.Dynamics

variable {n : ℕ}

/-- Diagonal degradation/dilution as a continuous linear map `v ↦ (fun i => γ i • v i)`. -/
def degCLM (γ : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => γ i • ContinuousLinearMap.proj i)

@[simp] theorem degCLM_apply (γ : Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    degCLM γ v i = γ i * v i := by
  simp [degCLM]

/-- The assembled gene-regulatory vector field: production `e` minus degradation/dilution `γ`. -/
def field (γ : Fin n → ℝ) (e : (Fin n → ℝ) → (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun y => e y - degCLM γ y

@[simp] theorem field_apply (γ : Fin n → ℝ) (e : (Fin n → ℝ) → (Fin n → ℝ))
    (y : Fin n → ℝ) (i : Fin n) : field γ e y i = e y i - γ i * y i := by
  simp only [field, Pi.sub_apply, degCLM_apply]

/-- The field's derivative at `x` is the production derivative minus the (constant, linear)
degradation map. -/
theorem hasFDerivAt_field {γ : Fin n → ℝ} {e : (Fin n → ℝ) → (Fin n → ℝ)}
    {E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {x : Fin n → ℝ} (he : HasFDerivAt e E x) :
    HasFDerivAt (field γ e) (E - degCLM γ) x :=
  he.sub (degCLM γ).hasFDerivAt

/-- The negated field, whose zeros coincide with the field's steady states but whose Jacobian carries the
degradation on its (positive) diagonal, the orientation Gale–Nikaido needs. -/
def negField (γ : Fin n → ℝ) (e : (Fin n → ℝ) → (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun y => degCLM γ y - e y

theorem hasFDerivAt_negField {γ : Fin n → ℝ} {e : (Fin n → ℝ) → (Fin n → ℝ)}
    {E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {x : Fin n → ℝ} (he : HasFDerivAt e E x) :
    HasFDerivAt (negField γ e) (degCLM γ - E) x :=
  (degCLM γ).hasFDerivAt.sub he

open scoped Matrix

/-- `jacobianMatrix` is additive, since `LinearMap.toMatrix'` is. -/
theorem jacobianMatrix_sub (A B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    jacobianMatrix (A - B) = jacobianMatrix A - jacobianMatrix B := by
  simp only [jacobianMatrix, ContinuousLinearMap.toLinearMap_sub, map_sub]

/-- The degradation map's Jacobian is the diagonal of degradation rates. -/
theorem jacobianMatrix_degCLM (γ : Fin n → ℝ) : jacobianMatrix (degCLM γ) = Matrix.diagonal γ := by
  ext i j
  simp only [jacobianMatrix, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, degCLM_apply,
    Pi.single_apply, Matrix.diagonal_apply, mul_ite, mul_one, mul_zero]

/-- **Assembled-ODE sensor (Gale–Nikaido).** For a feedforward (acyclic) production (species `i`
produced only by strictly earlier species `j < i`, encoded as the production Jacobian vanishing on and
above the diagonal), the assembled field has at most one steady state on any concentration box: its
dose-response has a unique operating point, for all parameterizations. -/
theorem assembled_sensor_unique {γ : Fin n → ℝ} {e : (Fin n → ℝ) → (Fin n → ℝ)}
    {E : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))} {lo hi : Fin n → ℝ}
    (hγ : ∀ i, 0 < γ i)
    (hE : ∀ z ∈ Set.Icc lo hi, HasFDerivAt e (E z) z)
    (htri : ∀ z ∈ Set.Icc lo hi, ∀ i j : Fin n, i ≤ j → jacobianMatrix (E z) i j = 0)
    {a b : Fin n → ℝ} (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hab : field γ e a = field γ e b) : a = b := by
  have hF : ∀ z ∈ Set.Icc lo hi, HasFDerivAt (negField γ e) (degCLM γ - E z) z :=
    fun z hz => hasFDerivAt_negField (hE z hz)
  have hP : ∀ z ∈ Set.Icc lo hi, (jacobianMatrix (degCLM γ - E z)).IsPMatrix := by
    intro z hz
    rw [jacobianMatrix_sub, jacobianMatrix_degCLM]
    apply isPMatrix_of_lowerTriangular
    · intro i j hji
      have h1 : jacobianMatrix (E z) j i = 0 := htri z hz j i (le_of_lt hji)
      have h2 : (j : Fin n) ≠ i := ne_of_lt hji
      simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.diagonal_apply, if_neg h2, h1,
        sub_zero]
    · intro i
      have h0 : jacobianMatrix (E z) i i = 0 := htri z hz i i (le_refl i)
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, h0, sub_zero]
      exact hγ i
  have hnab : negField γ e a = negField γ e b := by
    have hneg : ∀ y : Fin n → ℝ, negField γ e y = - field γ e y := by
      intro y; funext i; simp only [negField, field, Pi.sub_apply, Pi.neg_apply, degCLM_apply]; ring
    rw [hneg a, hneg b, hab]
  exact unique_equilibrium_of_pmatrix hF hP ha hb hnab

/-- **Forward-invariant concentration orthant (Nagumo).** With nonnegative production, any solution of
the assembled field that starts with all species nonnegative stays nonnegative for all forward time. The
concentrations never leave the physical region. Proved per coordinate from crnt-lean's scalar Nagumo
half-space lemma: where a species hits zero, degradation cannot push it negative because production is
nonnegative. -/
theorem nonneg_orthant_invariant {γ : Fin n → ℝ} {e : (Fin n → ℝ) → (Fin n → ℝ)}
    (he_nonneg : ∀ x i, 0 ≤ e x i) {c : ℝ → (Fin n → ℝ)}
    (hderiv : ∀ t i, HasDerivAt (fun s => c s i) (field γ e (c t) i) t)
    (hc0 : ∀ i, 0 ≤ c 0 i) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ c t i := by
  intro t ht i
  refine CRNT.nagumo_halfspace_scalar (g := fun s => c s i) (L := γ i) ?_ ?_ ?_ t ht
  · intro s
    rw [(hderiv s i).deriv]
    exact hderiv s i
  · intro s _
    rw [(hderiv s i).deriv, field_apply, neg_mul]
    linarith [he_nonneg (c s) i]
  · exact hc0 i

end GRN.Dynamics
