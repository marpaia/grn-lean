import Mathlib
import GRN.Dynamics.Assembled
import GRN.Dynamics.GRNEc50
import GRN.Dynamics.TopoOrder

/-!
# The assembled GRN Jacobian

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

/-- **The assembled Hill production is Fréchet-differentiable** at a strictly positive state: differentiate
`valuation` / `opRate` / `hill` / `hill2` / `sum`, giving the assembled field derivative `F'`. -/
theorem hasFDerivAt_assembledProd (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (z : Fin n → ℝ) (hz : ∀ k, 0 < z k) :
    ∃ E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ), HasFDerivAt (g.assembledProd wp e) E z := by
  -- It suffices to establish differentiability; the derivative is then `fderiv`.
  suffices h : DifferentiableAt ℝ (g.assembledProd wp e) z from ⟨_, h.hasFDerivAt⟩
  -- Coordinate projections of the state are differentiable.
  have hproj : ∀ i : Fin n, DifferentiableAt ℝ (fun x : Fin n → ℝ => x i) z :=
    fun i => (differentiable_pi.mp differentiable_id i).differentiableAt
  -- A single normalized Hill factor `(φ·K⁻¹)^nn` is differentiable when the base is nonzero at `z`
  -- or the input is constant.  (Division is written multiplicatively so the general multivariable
  -- Fréchet lemmas apply.)
  have rpowD : ∀ (φ : (Fin n → ℝ) → ℝ) (K nn : ℝ), 0 < K → 0 ≤ φ z →
      DifferentiableAt ℝ φ z → (φ z ≠ 0 ∨ ∀ x, φ x = φ z) →
      DifferentiableAt ℝ (fun x => (φ x * K⁻¹) ^ nn) z := by
    intro φ K nn hK hnn hd hdisj
    rcases hdisj with hne | hcon
    · have hbase : DifferentiableAt ℝ (fun x => φ x * K⁻¹) z := DifferentiableAt.mul_const hd K⁻¹
      have hupos : 0 < φ z := lt_of_le_of_ne hnn (Ne.symm hne)
      exact DifferentiableAt.rpow_const hbase (Or.inl (by positivity))
    · have he : (fun x => (φ x * K⁻¹) ^ nn) = fun _ : Fin n → ℝ => (φ z * K⁻¹) ^ nn := by
        funext x; rw [hcon x]
      rw [he]; exact differentiableAt_const _
  -- A single-input Hill response is differentiable in an admissible input.
  have hillD : ∀ (a0 a1 K nn : ℝ) (φ : (Fin n → ℝ) → ℝ), 0 < K →
      0 ≤ φ z → DifferentiableAt ℝ φ z → (φ z ≠ 0 ∨ ∀ x, φ x = φ z) →
      DifferentiableAt ℝ (fun x => hill a0 a1 K nn (φ x)) z := by
    intro a0 a1 K nn φ hK hnn hd hdisj
    have hR : DifferentiableAt ℝ (fun x => (φ x * K⁻¹) ^ nn) z := rpowD φ K nn hK hnn hd hdisj
    have hbnn : 0 ≤ φ z * K⁻¹ := mul_nonneg hnn (inv_nonneg.2 hK.le)
    simp only [hill, div_eq_mul_inv]
    have hnum : DifferentiableAt ℝ (fun x => a0 + a1 * (φ x * K⁻¹) ^ nn) z :=
      (differentiableAt_const a0).add ((differentiableAt_const a1).mul hR)
    have hden : DifferentiableAt ℝ (fun x => 1 + (φ x * K⁻¹) ^ nn) z :=
      (differentiableAt_const 1).add hR
    have hdne : (1 : ℝ) + (φ z * K⁻¹) ^ nn ≠ 0 := by positivity
    exact hnum.mul (DifferentiableAt.inv hden hdne)
  -- The two-input Hill response is differentiable in two admissible inputs.
  have hill2D : ∀ (a0 a1 a2 a3 K1 K2 n1 n2 : ℝ) (φ ψ : (Fin n → ℝ) → ℝ),
      0 < K1 → 0 < K2 → 0 ≤ φ z → 0 ≤ ψ z →
      DifferentiableAt ℝ φ z → (φ z ≠ 0 ∨ ∀ x, φ x = φ z) →
      DifferentiableAt ℝ ψ z → (ψ z ≠ 0 ∨ ∀ x, ψ x = ψ z) →
      DifferentiableAt ℝ (fun x => hill2 a0 a1 a2 a3 K1 K2 n1 n2 (φ x) (ψ x)) z := by
    intro a0 a1 a2 a3 K1 K2 n1 n2 φ ψ hK1 hK2 hφnn hψnn hφd hφdisj hψd hψdisj
    have hR1 : DifferentiableAt ℝ (fun x => (φ x * K1⁻¹) ^ n1) z := rpowD φ K1 n1 hK1 hφnn hφd hφdisj
    have hR2 : DifferentiableAt ℝ (fun x => (ψ x * K2⁻¹) ^ n2) z := rpowD ψ K2 n2 hK2 hψnn hψd hψdisj
    have hb1nn : 0 ≤ φ z * K1⁻¹ := mul_nonneg hφnn (inv_nonneg.2 hK1.le)
    have hb2nn : 0 ≤ ψ z * K2⁻¹ := mul_nonneg hψnn (inv_nonneg.2 hK2.le)
    simp only [hill2, div_eq_mul_inv]
    have hnum : DifferentiableAt ℝ (fun x =>
        a0 + a1 * (φ x * K1⁻¹) ^ n1 + a2 * (ψ x * K2⁻¹) ^ n2
          + a3 * ((φ x * K1⁻¹) ^ n1 * (ψ x * K2⁻¹) ^ n2)) z :=
      (((differentiableAt_const a0).add ((differentiableAt_const a1).mul hR1)).add
        ((differentiableAt_const a2).mul hR2)).add
        ((differentiableAt_const a3).mul (hR1.mul hR2))
    have hden : DifferentiableAt ℝ (fun x =>
        1 + (φ x * K1⁻¹) ^ n1 + (ψ x * K2⁻¹) ^ n2 + (φ x * K1⁻¹) ^ n1 * (ψ x * K2⁻¹) ^ n2) z :=
      (((differentiableAt_const 1).add hR1).add hR2).add (hR1.mul hR2)
    have hdne : (1 : ℝ) + (φ z * K1⁻¹) ^ n1 + (ψ z * K2⁻¹) ^ n2
        + (φ z * K1⁻¹) ^ n1 * (ψ z * K2⁻¹) ^ n2 ≠ 0 := by positivity
    exact hnum.mul (DifferentiableAt.inv hden hdne)
  -- Each valued input slot (a `getD k` into the mapped valuations) is admissible: differentiable at
  -- `z`, nonnegative there, and either strictly positive (a state coordinate) or constant (an inducer).
  have slotGet : ∀ (op : Node) (k : ℕ),
      DifferentiableAt ℝ (fun x : Fin n → ℝ =>
        ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0) z ∧
      0 ≤ ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => z (e.symm j)))).getD k 0 ∧
      (((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => z (e.symm j)))).getD k 0 ≠ 0 ∨
        ∀ x : Fin n → ℝ,
          ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0 =
          ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => z (e.symm j)))).getD k 0) := by
    intro op k
    rcases hget : (g.inputsOf op.id)[k]? with _ | id
    · -- Index out of range: the slot is constantly `0`.
      have hz0 : ∀ x : Fin n → ℝ,
          ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0 = 0 := by
        intro x; rw [List.getD_eq_getElem?_getD, List.getElem?_map, hget]; rfl
      refine ⟨?_, ?_, ?_⟩
      · have he : (fun x : Fin n → ℝ =>
            ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0)
            = fun _ => (0 : ℝ) := funext hz0
        rw [he]; exact differentiableAt_const 0
      · exact (hz0 z).ge
      · right; intro x; rw [hz0 x, hz0 z]
    · -- Index `k` reads input id `id`.
      have hval : ∀ x : Fin n → ℝ,
          ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0
          = g.valuation wp.inducer (fun j => x (e.symm j)) id := by
        intro x; rw [List.getD_eq_getElem?_getD, List.getElem?_map, hget]; rfl
      by_cases hid : id ∈ g.regIds
      · -- A regulated species: the slot is a (strictly positive) state coordinate.
        have hpr : ∀ x : Fin n → ℝ,
            g.valuation wp.inducer (fun j => x (e.symm j)) id = x (e.symm ⟨id, hid⟩) := by
          intro x; simp only [GRN.valuation, dif_pos hid]
        have hpos : 0 < z (e.symm ⟨id, hid⟩) := hz _
        refine ⟨?_, ?_, ?_⟩
        · have he : (fun x : Fin n → ℝ =>
              ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0)
              = fun x => x (e.symm ⟨id, hid⟩) := by funext x; rw [hval x, hpr x]
          rw [he]; exact hproj _
        · rw [hval z, hpr z]; exact hpos.le
        · left; rw [hval z, hpr z]; exact ne_of_gt hpos
      · -- An external inducer: the slot is constant.
        have hcs : ∀ x : Fin n → ℝ,
            g.valuation wp.inducer (fun j => x (e.symm j)) id = wp.inducer id := by
          intro x; simp only [GRN.valuation, dif_neg hid]
        refine ⟨?_, ?_, ?_⟩
        · have he : (fun x : Fin n → ℝ =>
              ((g.inputsOf op.id).map (g.valuation wp.inducer (fun j => x (e.symm j)))).getD k 0)
              = fun _ => wp.inducer id := by funext x; rw [hval x, hcs x]
          rw [he]; exact differentiableAt_const _
        · rw [hval z, hcs z]; exact wp.inducer_nonneg id
        · right; intro x; rw [hval x, hcs x, hval z, hcs z]
  -- `headD 0` agrees with `getD 0 0`, so the single-input slot reuses `slotGet _ 0`.
  have headD_getD : ∀ L : List ℝ, L.headD 0 = L.getD 0 0 := by intro L; cases L <;> rfl
  -- Every operator's rate is differentiable at `z`.
  have hopD : ∀ op ∈ g.operators,
      DifferentiableAt ℝ (fun x : Fin n → ℝ =>
        g.opRate (g.valuation wp.inducer (fun j => x (e.symm j))) op) z := by
    intro op hop
    rcases hk : op.kind with _ | _ | _ | _ | _ | _ | _ | _ <;>
      simp only [opRate, opRateV, hk]
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · -- receiver
      simp only [headD_getD]
      obtain ⟨hd0, hnn0, hdisj0⟩ := slotGet op 0
      exact hillD _ _ _ _ _ (wp.K_pos op hop) hnn0 hd0 hdisj0
    · -- hill1
      simp only [headD_getD]
      obtain ⟨hd0, hnn0, hdisj0⟩ := slotGet op 0
      exact hillD _ _ _ _ _ (wp.K_pos op hop) hnn0 hd0 hdisj0
    · -- hill2
      obtain ⟨hd0, hnn0, hdisj0⟩ := slotGet op 0
      obtain ⟨hd1, hnn1, hdisj1⟩ := slotGet op 1
      exact hill2D _ _ _ _ _ _ _ _ _ _ (wp.K1_pos op hop) (wp.K2_pos op hop)
        hnn0 hnn1 hd0 hdisj0 hd1 hdisj1
    · -- sum
      simp only [List.length_map]
      generalize List.range (g.inputsOf op.id).length = R
      induction R with
      | nil => simp only [List.map_nil, List.sum_nil]; exact differentiableAt_const 0
      | cons idx t ih =>
        simp only [List.map_cons, List.sum_cons]
        refine DifferentiableAt.add ?_ ih
        obtain ⟨hd, hnn, hdisj⟩ := slotGet op idx
        exact hillD _ _ _ _ _ (wp.sum_wp op hop idx).2.2.1 hnn hd hdisj
  -- A finite list sum of differentiable operator rates is differentiable.
  have hsumD : ∀ L : List Node, (∀ op ∈ L, op ∈ g.operators) →
      DifferentiableAt ℝ (fun x : Fin n → ℝ =>
        (L.map (g.opRate (g.valuation wp.inducer (fun j => x (e.symm j))))).sum) z := by
    intro L
    induction L with
    | nil => intro _; simp only [List.map_nil, List.sum_nil]; exact differentiableAt_const 0
    | cons a t ih =>
      intro hL
      simp only [List.map_cons, List.sum_cons]
      exact (hopD a (hL a List.mem_cons_self)).add (ih (fun op hop => hL op (List.mem_cons_of_mem a hop)))
  -- Assemble: componentwise (over `Fin n`), then per-species over the producing operators.
  refine differentiableAt_pi.mpr (fun k => ?_)
  unfold GRN.assembledProd GRN.prodOf
  exact hsumD _ (fun op hop => List.mem_of_mem_filter hop)

/-- **The assembled Jacobian is triangular.** Under a topological enumeration (`regulates (e k) (e l) →
k < l`), the negated-field Jacobian `negJac` is block-triangular for the identity order, with a strictly
positive (degradation) diagonal. -/
theorem negJac_blockTriangular (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (htopo : ∀ k l : Fin n, g.regulates (e k) (e l) → k < l)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) :
    (g.negJac wp e E).transpose.BlockTriangular id ∧ ∀ k, 0 < g.negJac wp e E k k := by
  classical
  -- The interpreted production of a species depends on the state only through the species that
  -- regulate it: perturbing a non-regulating coordinate leaves the production unchanged.
  have hprod : ∀ (i : g.Species) (s s' : g.Species → ℝ),
      (∀ j, g.regulates j i → s j = s' j) →
      g.prodOf wp.inducer i s = g.prodOf wp.inducer i s' := by
    intro i s s' hagree
    simp only [GRN.prodOf]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro op hop
    have hi : (i : String) ∈ g.outputsOf op.id :=
      of_decide_eq_true (List.mem_filter.1 hop).2
    have hopmem : op ∈ g.operators := List.mem_of_mem_filter hop
    simp only [GRN.opRate]
    congr 1
    apply List.map_congr_left
    intro id hid
    simp only [GRN.valuation]
    by_cases h : id ∈ g.regIds
    · simp only [dif_pos h]
      exact hagree ⟨id, h⟩ ⟨op, hopmem, hid, hi⟩
    · simp only [dif_neg h]
  -- The production Jacobian entry `(r, c)` vanishes whenever `e c` does not regulate `e r`: the
  -- `c`-directional derivative of coordinate `r` is the derivative of a constant.
  have hzero : ∀ r c : Fin n, ¬ g.regulates (e c) (e r) → jacobianMatrix E r c = 0 := by
    intro r c hnr
    set v : Fin n → ℝ := Pi.single c 1 with hv
    have hconst : ∀ t : ℝ,
        g.assembledProd wp e (z + t • v) r = g.assembledProd wp e z r := by
      intro t
      simp only [GRN.assembledProd]
      apply hprod
      intro j hj
      have hjc : j ≠ e c := by
        rintro rfl
        exact hnr hj
      have hsymm : e.symm j ≠ c := by
        intro hc
        apply hjc
        have h1 := e.apply_symm_apply j
        rw [hc] at h1
        exact h1.symm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv, Pi.single_apply, if_neg hsymm,
        mul_zero, add_zero]
    have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
      exact h1.const_add z
    have hcomp : HasDerivAt (fun t : ℝ => g.assembledProd wp e (z + t • v)) (E v) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (f := fun t : ℝ => z + t • v) (x := (0 : ℝ))
        hE hline (by simp)
    have hcompr : HasDerivAt (fun t : ℝ => g.assembledProd wp e (z + t • v) r) (E v r) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq
        (f := fun t : ℝ => g.assembledProd wp e (z + t • v)) (x := (0 : ℝ))
        (ContinuousLinearMap.proj r : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt hcomp rfl
    have hderiv0 : HasDerivAt (fun t : ℝ => g.assembledProd wp e (z + t • v) r) 0 0 := by
      have hcongr : (fun t : ℝ => g.assembledProd wp e (z + t • v) r)
          = fun _ => g.assembledProd wp e z r := funext hconst
      rw [hcongr]
      exact hasDerivAt_const _ _
    have hEvr : E v r = 0 := hcompr.unique hderiv0
    have hjac : jacobianMatrix E r c = E v r := by
      rw [hv]
      simp only [jacobianMatrix, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    rw [hjac]; exact hEvr
  -- The negated-field Jacobian is degradation (a positive diagonal) minus the production Jacobian.
  have hM : g.negJac wp e E
      = Matrix.diagonal (fun k => wp.γ (e k)) - jacobianMatrix E := by
    simp only [GRN.negJac]
    rw [jacobianMatrix_sub, jacobianMatrix_degCLM]
  refine ⟨?_, ?_⟩
  · -- Block-triangular: below-diagonal entries of `negJac` (row `j` < col `i`) vanish, since a
    -- regulating edge `e i → e j` would force `i < j`.
    intro i j hji
    have hji' : j < i := hji
    have hnr : ¬ g.regulates (e i) (e j) :=
      fun hr => lt_irrefl i (lt_trans (htopo i j hr) hji')
    rw [Matrix.transpose_apply, hM, Matrix.sub_apply, Matrix.diagonal_apply,
      if_neg (ne_of_lt hji'), hzero j i hnr, sub_zero]
  · -- Positive diagonal: the diagonal entry is the (positive) degradation rate, the production
    -- Jacobian's diagonal being zero (a self-edge would force `k < k`).
    intro k
    rw [hM, Matrix.sub_apply, Matrix.diagonal_apply_eq]
    have hnr : ¬ g.regulates (e k) (e k) := fun hr => lt_irrefl k (htopo k k hr)
    rw [hzero k k hnr, sub_zero]
    exact wp.γ_pos (e k)

/-- **The assembled sensor has a unique equilibrium.** Feeding the triangular Jacobian through
`isPMatrix_of_lowerTriangular` and `unique_equilibrium_of_pmatrix`: for an acyclic, well-posed GRN with a
topological enumeration, the assembled field has at most one steady state on any concentration box. -/
theorem grn_assembled_sensor_unique (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (htopo : ∀ k l : Fin n, g.regulates (e k) (e l) → k < l) (lo hi : Fin n → ℝ)
    (hlo : ∀ k, 0 < lo k)
    {a b : Fin n → ℝ} (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hab : Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) a
         = Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) b) :
    a = b := by
  classical
  -- Every point of the concentration box is strictly positive, so the assembled Hill production is
  -- Fréchet-differentiable there; choose the production derivative `E z` at each box point.
  have hex : ∀ z, z ∈ Set.Icc lo hi → ∃ E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
      HasFDerivAt (g.assembledProd wp e) E z := by
    intro z hz
    exact g.hasFDerivAt_assembledProd wp hreg e z (fun k => lt_of_lt_of_le (hlo k) (hz.1 k))
  choose! E hE using hex
  -- The negated field carries degradation on its (positive) diagonal; its derivative is `degCLM γ − E z`.
  have hF : ∀ z ∈ Set.Icc lo hi,
      HasFDerivAt (Dynamics.negField (fun k => wp.γ (e k)) (g.assembledProd wp e))
        (Dynamics.degCLM (fun k => wp.γ (e k)) - E z) z :=
    fun z hz => Dynamics.hasFDerivAt_negField (hE z hz)
  -- Under the topological enumeration that Jacobian is lower-triangular with positive diagonal, hence a
  -- P-matrix (Gale–Nikaido's hypothesis).
  have hP : ∀ z ∈ Set.Icc lo hi,
      (jacobianMatrix (Dynamics.degCLM (fun k => wp.γ (e k)) - E z)).IsPMatrix := by
    intro z hz
    obtain ⟨hUT, hdiag⟩ := g.negJac_blockTriangular wp hreg e htopo (E z) z (hE z hz)
    exact isPMatrix_of_lowerTriangular hUT hdiag
  -- The field's steady states are the negated field's steady states.
  have hneg : Dynamics.negField (fun k => wp.γ (e k)) (g.assembledProd wp e)
            = fun y => -Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) y := by
    funext y i
    simp only [Dynamics.negField, Dynamics.field, Pi.sub_apply, Pi.neg_apply]
    ring
  have hnab : Dynamics.negField (fun k => wp.γ (e k)) (g.assembledProd wp e) a
            = Dynamics.negField (fun k => wp.γ (e k)) (g.assembledProd wp e) b := by
    simp only [hneg, hab]
  exact unique_equilibrium_of_pmatrix
    (F := Dynamics.negField (fun k => wp.γ (e k)) (g.assembledProd wp e))
    (F' := fun z => Dynamics.degCLM (fun k => wp.γ (e k)) - E z) hF hP ha hb hnab

/-- **The assembled sensor of an acyclic GRN has a unique equilibrium.** The topological enumeration
`topoEquiv` and its regulation-monotonicity `topoEquiv_regulates_lt` discharge the enumeration
hypotheses of `grn_assembled_sensor_unique`, so an acyclic, well-posed, regular GRN has at most one
steady state on any concentration box. -/
theorem grn_assembled_sensor_unique_acyclic (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular)
    (lo hi : Fin (Fintype.card g.Species) → ℝ) (hlo : ∀ k, 0 < lo k)
    {a b : Fin (Fintype.card g.Species) → ℝ}
    (ha : a ∈ Set.Icc lo hi) (hb : b ∈ Set.Icc lo hi)
    (hab : Dynamics.field (fun k => wp.γ (g.topoEquiv hac k)) (g.assembledProd wp (g.topoEquiv hac)) a
         = Dynamics.field (fun k => wp.γ (g.topoEquiv hac k))
             (g.assembledProd wp (g.topoEquiv hac)) b) :
    a = b :=
  g.grn_assembled_sensor_unique hac wp hreg (g.topoEquiv hac) (g.topoEquiv_regulates_lt hac)
    lo hi hlo ha hb hab

end GRN
