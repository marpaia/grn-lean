import Mathlib
import GRN.Dynamics.Interpret
import GRN.Dynamics.GRNEc50

/-!
# Reachability discharges strict monotonicity of the dose-response

`grn_reporter_ec50` (`GRN.Dynamics.GRNEc50`) delivers a unique EC50 for an acyclic, well-posed, `Regular`
GRN once the reporter's dose-response is **strictly monotone** in the chosen inducer. That last hypothesis
is topology-dependent (a flat circuit genuinely has no unique EC50), so it is left to the caller there.

This file discharges it from graph data alone. A **strict monotone path** from the inducer to the reporter,
a chain of regulation edges each carried by a strictly-activating operator, makes the reporter's steady
level strictly increasing in the inducer, hence the EC50 is unique from the wiring.

The strict carriers are single-input Hill/receiver activators and two-input `hill2` operators that activate
strictly in the driving port; `sum` operators, and non-strict operators, may appear elsewhere as
`MonoActivating` side-branches (they supply the ambient weak order). The engine is
`steadyFam_lt_base` / `steadyFam_lt_step` (`GRN.Dynamics.Feedforward`), chained along the path.
-/

set_option maxHeartbeats 1600000

namespace GRN

open GRN.Dynamics Set

/-! ## Strict two-input Hill monotonicity -/

/-- The two-input Hill response is **strictly** increasing in its first input when it activates strictly
in the base pair (`a0 < a1`), activates in the second (`a2 ≤ a3`), and the first Hill exponent is
positive. -/
theorem hill2_strictMonoOn_left {a0 a1 a2 a3 K1 K2 n1 n2 u2 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 < n1) (hu2 : 0 ≤ u2)
    (ha : a0 < a1) (ha' : a2 ≤ a3) :
    StrictMonoOn (fun u1 => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  simp only [hill2]
  set r2 := (u2 / K2) ^ n2
  set ru := (u / K1) ^ n1
  set rv := (v / K1) ^ n1
  have hr2 : 0 ≤ r2 := Real.rpow_nonneg (div_nonneg hu2 hK2.le) n2
  have hru : 0 ≤ ru := Real.rpow_nonneg (div_nonneg hu hK1.le) n1
  have hrlt : ru < rv := by
    apply Real.rpow_lt_rpow (div_nonneg hu hK1.le) _ hn1
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_lt_mul_of_pos_right huv (inv_pos.2 hK1)
  have hrv : 0 ≤ rv := le_of_lt (lt_of_le_of_lt hru hrlt)
  have hdu : (0:ℝ) < 1 + ru + r2 + ru * r2 := by nlinarith [mul_nonneg hru hr2]
  have hdv : (0:ℝ) < 1 + rv + r2 + rv * r2 := by nlinarith [mul_nonneg hrv hr2]
  rw [← sub_pos, div_sub_div _ _ (ne_of_gt hdv) (ne_of_gt hdu)]
  apply div_pos
  · nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 hrlt),
      mul_nonneg (mul_pos (sub_pos.2 ha) (sub_pos.2 hrlt)).le hr2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr2) (sub_pos.2 hrlt).le,
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr2) hr2) (sub_pos.2 hrlt).le]
  · exact mul_pos hdv hdu

/-- The two-input Hill response is **strictly** increasing in its second input when it activates strictly
in the base pair (`a0 < a2`), activates in the first (`a1 ≤ a3`), and the second Hill exponent is
positive. -/
theorem hill2_strictMonoOn_right {a0 a1 a2 a3 K1 K2 n1 n2 u1 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn2 : 0 < n2) (hu1 : 0 ≤ u1)
    (ha : a0 < a2) (ha' : a1 ≤ a3) :
    StrictMonoOn (fun u2 => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  simp only [hill2]
  set r1 := (u1 / K1) ^ n1
  set ru := (u / K2) ^ n2
  set rv := (v / K2) ^ n2
  have hr1 : 0 ≤ r1 := Real.rpow_nonneg (div_nonneg hu1 hK1.le) n1
  have hru : 0 ≤ ru := Real.rpow_nonneg (div_nonneg hu hK2.le) n2
  have hrlt : ru < rv := by
    apply Real.rpow_lt_rpow (div_nonneg hu hK2.le) _ hn2
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_lt_mul_of_pos_right huv (inv_pos.2 hK2)
  have hrv : 0 ≤ rv := le_of_lt (lt_of_le_of_lt hru hrlt)
  have hdu : (0:ℝ) < 1 + r1 + ru + r1 * ru := by nlinarith [mul_nonneg hr1 hru]
  have hdv : (0:ℝ) < 1 + r1 + rv + r1 * rv := by nlinarith [mul_nonneg hr1 hrv]
  rw [← sub_pos, div_sub_div _ _ (ne_of_gt hdv) (ne_of_gt hdu)]
  apply div_pos
  · nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 hrlt),
      mul_nonneg (mul_pos (sub_pos.2 ha) (sub_pos.2 hrlt)).le hr1,
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr1) (sub_pos.2 hrlt).le,
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr1) hr1) (sub_pos.2 hrlt).le]
  · exact mul_pos hdv hdu

/-! ## List indexing helpers -/

/-- Reading the mapped list at a resolved index. -/
theorem getD_map_of_getElem? {l : List String} {k : ℕ} {jid : String}
    (h : l[k]? = some jid) (f : String → ℝ) : (l.map f).getD k 0 = f jid := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]; rfl

/-- Reading the head of the mapped list at a resolved zeroth index. -/
theorem headD_map_of_getElem? {l : List String} {jid : String}
    (h : l[0]? = some jid) (f : String → ℝ) : (l.map f).headD 0 = f jid := by
  rw [List.headD_eq_getD]; exact getD_map_of_getElem? h f

/-! ## Strict activation at a port -/

/-- An operator is **strictly activating at input port `k`**: its rate strictly increases when the
port-`k` input strictly increases (with the other inputs held or weakly rising). Single-input
Hill/receiver strictly activate at port `0` (`a0 < a1`, `0 < n`); a two-input `hill2` strictly activates
at port `0` (`a0 < a1`) or port `1` (`a0 < a2`) when it is `MonoActivating` and the corresponding Hill
exponent is positive. -/
def _root_.Node.StrictActivatingAt (op : Node) (k : ℕ) : Prop :=
  match op.kind with
  | .receiver | .hill1 =>
      k = 0 ∧ 0 < op.rparam "K" 1 ∧ 0 < op.rparam "n" 2 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 < (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0
  | .hill2 =>
      op.MonoActivating ∧
      ((k = 0 ∧ 0 < (op.rlist "n").getD 0 2 ∧
          (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 <
            (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0) ∨
       (k = 1 ∧ 0 < (op.rlist "n").getD 1 2 ∧
          (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 <
            (op.alphaNums.map (fun q => (q : ℝ))).getD 2 0))
  | _ => False

/-- A strictly-activating operator is `MonoActivating` (its rate is weakly monotone in every input). -/
theorem Node.StrictActivatingAt.monoActivating {op : Node} {k : ℕ} (h : op.StrictActivatingAt k) :
    op.MonoActivating := by
  rcases hk : op.kind with _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [Node.StrictActivatingAt, hk] at h <;> simp only [Node.MonoActivating, hk]
  · exact ⟨h.2.1, h.2.2.1.le, h.2.2.2.le⟩
  · exact ⟨h.2.1, h.2.2.1.le, h.2.2.2.le⟩
  · simp only [Node.MonoActivating, hk] at h; exact h.1

/-- **A strictly-activating operator's rate strictly rises** when its port-`k` input strictly rises and
its inputs weakly rise. -/
theorem opRate_strictMono_at (g : GRN) (op : Node) {val₁ val₂ : String → ℝ} {k : ℕ} {jid : String}
    (hstr : op.StrictActivatingAt k) (hk : (g.inputsOf op.id)[k]? = some jid)
    (hnn : ∀ id ∈ g.inputsOf op.id, 0 ≤ val₁ id)
    (hle : ∀ id ∈ g.inputsOf op.id, val₁ id ≤ val₂ id)
    (hjs : val₁ jid < val₂ jid) : g.opRate val₁ op < g.opRate val₂ op := by
  have hjmem : jid ∈ g.inputsOf op.id := List.mem_of_getElem? hk
  have hj1 : 0 ≤ val₁ jid := hnn jid hjmem
  have hj2 : 0 ≤ val₂ jid := le_trans hj1 hjs.le
  rcases hkind : op.kind with _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [Node.StrictActivatingAt, hkind] at hstr
  · -- receiver
    obtain ⟨hk0, hK, hn, ha⟩ := hstr; subst hk0
    simp only [opRate, opRateV, hkind]
    rw [headD_map_of_getElem? hk val₁, headD_map_of_getElem? hk val₂]
    exact hill_strictMonoOn hK hn ha (mem_Ici.2 hj1) (mem_Ici.2 hj2) hjs
  · -- hill1
    obtain ⟨hk0, hK, hn, ha⟩ := hstr; subst hk0
    simp only [opRate, opRateV, hkind]
    rw [headD_map_of_getElem? hk val₁, headD_map_of_getElem? hk val₂]
    exact hill_strictMonoOn hK hn ha (mem_Ici.2 hj1) (mem_Ici.2 hj2) hjs
  · -- hill2
    obtain ⟨hMA, hcase⟩ := hstr
    simp only [Node.MonoActivating, hkind] at hMA
    obtain ⟨hK1, hK2, hn1, hn2, h01, h23, h02, h13⟩ := hMA
    simp only [opRate, opRateV, hkind]
    have hg1nn1 : 0 ≤ ((g.inputsOf op.id).map val₁).getD 1 0 := getD_map_nonneg' hnn 1
    have hg0nn1 : 0 ≤ ((g.inputsOf op.id).map val₁).getD 0 0 := getD_map_nonneg' hnn 0
    have hg1le : ((g.inputsOf op.id).map val₁).getD 1 0 ≤ ((g.inputsOf op.id).map val₂).getD 1 0 :=
      getD_map_mono hle 1
    have hg0le : ((g.inputsOf op.id).map val₁).getD 0 0 ≤ ((g.inputsOf op.id).map val₂).getD 0 0 :=
      getD_map_mono hle 0
    rcases hcase with ⟨hk0, hn1s, ha01s⟩ | ⟨hk1, hn2s, ha02s⟩
    · subst hk0
      rw [getD_map_of_getElem? hk val₁, getD_map_of_getElem? hk val₂]
      exact lt_of_lt_of_le
        (hill2_strictMonoOn_left hK1 hK2 hn1s hg1nn1 ha01s h23 (mem_Ici.2 hj1) (mem_Ici.2 hj2) hjs)
        (hill2_monotoneOn_right hK1 hK2 hn2 hj2 h02 h13 (mem_Ici.2 hg1nn1)
          (mem_Ici.2 (le_trans hg1nn1 hg1le)) hg1le)
    · subst hk1
      rw [getD_map_of_getElem? hk val₁, getD_map_of_getElem? hk val₂]
      exact lt_of_lt_of_le
        (hill2_strictMonoOn_right hK1 hK2 hn2s hg0nn1 ha02s h13 (mem_Ici.2 hj1) (mem_Ici.2 hj2) hjs)
        (hill2_monotoneOn_left hK1 hK2 hn1 hj2 h01 h23 (mem_Ici.2 hg0nn1)
          (mem_Ici.2 (le_trans hg0nn1 hg0le)) hg0le)

/-! ## Valuation monotonicity helpers -/

/-- Raising the inducer weakly raises every valuation. -/
theorem valuation_mono_inducer (g : GRN) (x : g.Species → ℝ) {ind₁ ind₂ : String → ℝ}
    (h : ∀ id, ind₁ id ≤ ind₂ id) (id : String) :
    g.valuation ind₁ x id ≤ g.valuation ind₂ x id := by
  unfold valuation; split
  · exact le_refl _
  · exact h id

/-- Raising the state weakly raises every valuation. -/
theorem valuation_mono_state (g : GRN) (ind : String → ℝ) {x y : g.Species → ℝ}
    (h : ∀ j, x j ≤ y j) (id : String) :
    g.valuation ind x id ≤ g.valuation ind y id := by
  unfold valuation; split
  · exact h _
  · exact le_refl _

/-- A species reads its own state coordinate through the valuation. -/
theorem valuation_species (g : GRN) (ind : String → ℝ) (z : g.Species → ℝ) (j : g.Species) :
    g.valuation ind z (j : String) = z j := by
  unfold valuation; rw [dif_pos j.2]

/-- Raising the inducer level weakly raises `inducerAt`. -/
theorem inducerAt_mono {base : String → ℝ} {s : String} {p q : ℝ} (hpq : p ≤ q) (id : String) :
    inducerAt base s p id ≤ inducerAt base s q id := by
  unfold inducerAt; split
  · exact hpq
  · exact le_refl _

/-! ## Production is strictly / weakly monotone with a strict carrier -/

/-- **Strict production from a strict carrier.** If one operator producing `i` is strictly activating in a
port whose input `jid` strictly rises, and every operator producing `i` is `MonoActivating` (so the rest
weakly rise), then `i`'s production strictly rises. -/
theorem prodOf_lt (g : GRN) (i : g.Species)
    {ind₁ ind₂ : String → ℝ} {x₁ x₂ : g.Species → ℝ}
    (hnn : ∀ id, 0 ≤ g.valuation ind₁ x₁ id)
    (hle : ∀ id, g.valuation ind₁ x₁ id ≤ g.valuation ind₂ x₂ id)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating)
    {op₀ : Node} {k : ℕ} {jid : String} (hop₀ : op₀ ∈ g.operators)
    (hout : (i : String) ∈ g.outputsOf op₀.id) (hstr : op₀.StrictActivatingAt k)
    (hk : (g.inputsOf op₀.id)[k]? = some jid)
    (hjs : g.valuation ind₁ x₁ jid < g.valuation ind₂ x₂ jid) :
    g.prodOf ind₁ i x₁ < g.prodOf ind₂ i x₂ := by
  unfold prodOf
  refine List.sum_lt_sum _ _ ?_ ?_
  · intro op hop
    exact g.opRate_mono op (hMA op (List.mem_of_mem_filter hop)) (fun id _ => hnn id)
      (fun id _ => hle id)
  · refine ⟨op₀, List.mem_filter.2 ⟨hop₀, by simpa using hout⟩, ?_⟩
    exact g.opRate_strictMono_at op₀ hstr hk (fun id _ => hnn id) (fun id _ => hle id) hjs

/-- Raising the inducer weakly raises production. -/
theorem prodOf_le_inducer (g : GRN) (i : g.Species) (x : g.Species → ℝ)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating) (hxnn : ∀ j, 0 ≤ x j)
    {ind₁ ind₂ : String → ℝ} (hnn1 : ∀ id, 0 ≤ ind₁ id) (hile : ∀ id, ind₁ id ≤ ind₂ id) :
    g.prodOf ind₁ i x ≤ g.prodOf ind₂ i x := by
  unfold prodOf
  refine List.sum_le_sum (fun op hop => ?_)
  exact g.opRate_mono op (hMA op (List.mem_of_mem_filter hop))
    (fun id _ => g.valuation_nonneg hnn1 hxnn id) (fun id _ => g.valuation_mono_inducer x hile id)

/-- Production is monotone in the earlier (regulating) species. -/
theorem prodOf_mono_earlier (g : GRN) (i : g.Species) {x y : g.Species → ℝ}
    (hxnn : ∀ j, 0 ≤ x j) (hearlier : ∀ j, g.regulates j i → x j ≤ y j)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating) {ind : String → ℝ} (hnn : ∀ id, 0 ≤ ind id) :
    g.prodOf ind i x ≤ g.prodOf ind i y := by
  unfold prodOf
  refine List.sum_le_sum (fun op hop => ?_)
  have hmem : op ∈ g.operators := List.mem_of_mem_filter hop
  refine g.opRate_mono op (hMA op hmem) (fun id _ => g.valuation_nonneg hnn hxnn id) (fun id hid => ?_)
  unfold valuation; split
  · rename_i hmemid
    exact hearlier ⟨id, hmemid⟩ ⟨op, hmem, hid, by have := List.of_mem_filter hop; simpa using this⟩
  · exact le_refl _

/-- **The steady state is weakly monotone in the inducer level** (the ambient order the strict engine
needs), from `steadyFam_mono` on the interpreted production. -/
theorem grn_steadyFam_le (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed) (s : String)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (k : g.Species) :
    steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p k
    ≤ steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q k := by
  have hq : 0 ≤ q := le_trans hp hpq
  refine steadyFam_mono (g.regulates_wf hac) wp.γ_pos
    (fun i x hx => g.prodOf_nonneg (wp.setInducer s p hp) i x hx)
    (fun i x hx => g.prodOf_nonneg (wp.setInducer s q hq) i x hx)
    (fun i x hx => g.prodOf_le_inducer i x hMA hx (wp.setInducer s p hp).inducer_nonneg
      (fun id => inducerAt_mono hpq id))
    (fun i x y hx _ hxy => g.prodOf_mono_earlier i hx hxy hMA
      (wp.setInducer s q hq).inducer_nonneg) k

/-! ## The strict monotone path and its dose-response -/

/-- A **strict monotone regulation path** from the inducer id `s` to a species: a chain of regulation
edges each carried by a strictly-activating operator, from a species directly driven by `s` to the target.
The dose-response along such a path is strictly increasing in `s`, so the EC50 is unique. -/
inductive StrictPath (g : GRN) (s : String) : g.Species → Prop where
  | base (w : g.Species) {op : Node} (hop : op ∈ g.operators)
      (hout : (w : String) ∈ g.outputsOf op.id) {k : ℕ} (hstr : op.StrictActivatingAt k)
      (hk : (g.inputsOf op.id)[k]? = some s) : StrictPath g s w
  | step {u : g.Species} (w : g.Species) (hpath : StrictPath g s u) {op : Node}
      (hop : op ∈ g.operators) (hout : (w : String) ∈ g.outputsOf op.id) {k : ℕ}
      (hstr : op.StrictActivatingAt k) (hk : (g.inputsOf op.id)[k]? = some (u : String)) :
      StrictPath g s w

/-- **The dose-response strictly increases along a strict path.** For `0 ≤ p < q`, the target's steady
level at inducer `p` is strictly below that at `q`, by induction on the path: `steadyFam_lt_base` where `s`
drives the first species, `steadyFam_lt_step` at each strictly-activating edge, with `grn_steadyFam_le`
supplying the ambient weak order. -/
theorem strictPath_lt (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed) (s : String)
    (hsr : s ∉ g.regIds) (hMA : ∀ op ∈ g.operators, op.MonoActivating)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) (w : g.Species) (hpath : StrictPath g s w) :
    steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p w
    < steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q w := by
  have hq : 0 ≤ q := le_of_lt (lt_of_le_of_lt hp hpq)
  have hnnp : ∀ (k : g.Species) x, (∀ l, 0 ≤ x l) → 0 ≤ g.prodOf (inducerAt wp.inducer s p) k x :=
    fun k x hx => g.prodOf_nonneg (wp.setInducer s p hp) k x hx
  have hnnq : ∀ (k : g.Species) x, (∀ l, 0 ≤ x l) → 0 ≤ g.prodOf (inducerAt wp.inducer s q) k x :=
    fun k x hx => g.prodOf_nonneg (wp.setInducer s q hq) k x hx
  have hamb : ∀ k, steadyFam (g.regulates_wf hac) wp.γ
      (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p k
      ≤ steadyFam (g.regulates_wf hac) wp.γ
      (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q k :=
    fun k => g.grn_steadyFam_le hac wp s hMA hp (le_of_lt hpq) k
  induction hpath with
  | base w hop hout hstr hk =>
      refine steadyFam_lt_base (g.regulates_wf hac) wp.γ_pos hnnp hnnq hamb ?_ ?_
      · intro x y hx _ hxy
        exact g.prodOf_mono_earlier w hx hxy hMA (wp.setInducer s q hq).inducer_nonneg
      · intro x hx
        refine g.prodOf_lt w (fun id => g.valuation_nonneg (wp.setInducer s p hp).inducer_nonneg hx id)
          (fun id => g.valuation_mono_inducer x (fun id => inducerAt_mono (le_of_lt hpq) id) id)
          hMA hop hout hstr hk ?_
        have e1 : g.valuation (inducerAt wp.inducer s p) x s = p := by
          unfold valuation inducerAt; rw [dif_neg hsr, if_pos rfl]
        have e2 : g.valuation (inducerAt wp.inducer s q) x s = q := by
          unfold valuation inducerAt; rw [dif_neg hsr, if_pos rfl]
        rw [e1, e2]; exact hpq
  | step w hpath hop hout hstr hk ih =>
      rename_i u _ _
      have hrij : g.regulates u w := ⟨_, hop, List.mem_of_getElem? hk, hout⟩
      refine steadyFam_lt_step (g.regulates_wf hac) wp.γ_pos hrij hnnp hnnq hamb ?_ ?_ ih
      · intro x hx
        exact g.prodOf_le_inducer w x hMA hx (wp.setInducer s p hp).inducer_nonneg
          (fun id => inducerAt_mono (le_of_lt hpq) id)
      · intro x y hx _ hxy hlt
        refine g.prodOf_lt w (fun id => g.valuation_nonneg (wp.setInducer s q hq).inducer_nonneg hx id)
          (fun id => g.valuation_mono_state (inducerAt wp.inducer s q) hxy id) hMA hop hout hstr hk ?_
        rw [g.valuation_species, g.valuation_species]; exact hlt

/-- **Unique EC50 from a strict topological path.** For an acyclic, well-posed, `Regular` GRN whose
operators are all `MonoActivating`, a strict monotone path from an external inducer `s` to the reporter
`top` discharges the strict-monotonicity hypothesis of `grn_reporter_ec50`: the reporter's dose-response
has a unique EC50, read from the wiring with no hand-supplied kinetic inequality. -/
theorem grn_reporter_ec50_of_strictPath (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed) (s : String)
    (hsr : s ∉ g.regIds) (top : g.Species) (hreg : ∀ op ∈ g.operators, op.Regular)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating) (hpath : StrictPath g s top)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    {L : ℝ} (hL : L ∈ Set.Icc
      (steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) lo top)
      (steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) hi top)) :
    ∃! u, u ∈ Set.Icc lo hi ∧
      steadyFam (g.regulates_wf hac) wp.γ
        (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u top = L := by
  refine grn_reporter_ec50 g hac wp s top hreg hlo hle ?_ hL
  intro p hp q _ hpq
  exact g.strictPath_lt hac wp s hsr hMA (le_trans hlo hp.1) hpq top hpath

/-- **Unique EC50 for a direct sensor.** The single-edge specialization: when the reporter `top` is
produced by one operator that is strictly activating in the port fed directly by the inducer `s`, the
dose-response has a unique EC50. A `StrictPath.base` fed to `grn_reporter_ec50_of_strictPath`. -/
theorem grn_directSensor_ec50 (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed) (s : String)
    (hsr : s ∉ g.regIds) (top : g.Species) (hreg : ∀ op ∈ g.operators, op.Regular)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating) {op : Node} {k : ℕ} (hop : op ∈ g.operators)
    (hout : (top : String) ∈ g.outputsOf op.id) (hstr : op.StrictActivatingAt k)
    (hk : (g.inputsOf op.id)[k]? = some s) {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    {L : ℝ} (hL : L ∈ Set.Icc
      (steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) lo top)
      (steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) hi top)) :
    ∃! u, u ∈ Set.Icc lo hi ∧
      steadyFam (g.regulates_wf hac) wp.γ
        (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u top = L :=
  g.grn_reporter_ec50_of_strictPath hac wp s hsr top hreg hMA
    (StrictPath.base top hop hout hstr hk) hlo hle hL

end GRN
