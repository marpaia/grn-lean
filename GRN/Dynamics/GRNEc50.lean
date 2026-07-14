import Mathlib
import GRN.Dynamics.Interpret
import GRN.Dynamics.EC50

/-!
# General-GRN EC50 through the interpreter

For an arbitrary acyclic, well-posed `GRN`, the reporter's steady level as a function of a chosen
inducer's level has a **unique EC50**, obtained through the functor's real WF-recursion `steadyPoint`.

This discharges the abstract hypotheses of `steadyFam_ec50` for the interpreted production:
* **continuity**: `prodOf` is jointly continuous in `(inducer level, state)` on the nonnegative orthant,
  for every operator kind (`prodOf_param_continuousOn`);
* **monotonicity**: raising the inducer does not lower any steady value (via `opRate_mono` / `steady_le`);
* **strictness**: a strictly-activating drive from the inducer to the reporter makes the dose-response
  injective (the `steadyFam_lt_base` / `steadyFam_lt_step` engine).
-/

set_option maxHeartbeats 800000

namespace GRN

open GRN.Dynamics Set

/-! ## Continuity building blocks -/

/-- `headD` of a mapped valuation is continuous in the valuation. -/
theorem continuous_map_headD (l : List String) :
    Continuous (fun val : String → ℝ => (l.map val).headD 0) := by
  cases l with
  | nil => simpa using continuous_const
  | cons a t => simpa using continuous_apply a

/-- `getD k` of a mapped valuation is continuous in the valuation. -/
theorem continuous_map_getD (l : List String) (k : ℕ) :
    Continuous (fun val : String → ℝ => (l.map val).getD k 0) := by
  induction l generalizing k with
  | nil => simpa using continuous_const
  | cons a t ih =>
    cases k with
    | zero => simpa using continuous_apply a
    | succ k => simpa using ih k

/-- The two-input Hill response is continuous on the nonnegative quadrant. -/
theorem hill2_continuousOn {a0 a1 a2 a3 K1 K2 n1 n2 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) :
    ContinuousOn (fun p : ℝ × ℝ => hill2 a0 a1 a2 a3 K1 K2 n1 n2 p.1 p.2) (Ici 0 ×ˢ Ici 0) := by
  have hr1 : ContinuousOn (fun p : ℝ × ℝ => (p.1 / K1) ^ n1) (Ici 0 ×ˢ Ici 0) :=
    ((continuous_fst.div_const K1).continuousOn).rpow_const (fun _ _ => Or.inr hn1)
  have hr2 : ContinuousOn (fun p : ℝ × ℝ => (p.2 / K2) ^ n2) (Ici 0 ×ˢ Ici 0) :=
    ((continuous_snd.div_const K2).continuousOn).rpow_const (fun _ _ => Or.inr hn2)
  have hnum : ContinuousOn (fun p : ℝ × ℝ =>
      a0 + a1 * (p.1 / K1) ^ n1 + a2 * (p.2 / K2) ^ n2 + a3 * ((p.1 / K1) ^ n1 * (p.2 / K2) ^ n2))
      (Ici 0 ×ˢ Ici 0) :=
    ((continuousOn_const.add (continuousOn_const.mul hr1)).add (continuousOn_const.mul hr2)).add
      (continuousOn_const.mul (hr1.mul hr2))
  have hden : ContinuousOn (fun p : ℝ × ℝ =>
      1 + (p.1 / K1) ^ n1 + (p.2 / K2) ^ n2 + (p.1 / K1) ^ n1 * (p.2 / K2) ^ n2) (Ici 0 ×ˢ Ici 0) :=
    ((continuousOn_const.add hr1).add hr2).add (hr1.mul hr2)
  have hdenpos : ∀ p ∈ (Ici (0 : ℝ) ×ˢ Ici 0),
      (0 : ℝ) < 1 + (p.1 / K1) ^ n1 + (p.2 / K2) ^ n2 + (p.1 / K1) ^ n1 * (p.2 / K2) ^ n2 := by
    intro p hp
    have h1 : 0 ≤ (p.1 / K1) ^ n1 := Real.rpow_nonneg (div_nonneg (mem_prod.1 hp).1 hK1.le) n1
    have h2 : 0 ≤ (p.2 / K2) ^ n2 := Real.rpow_nonneg (div_nonneg (mem_prod.1 hp).2 hK2.le) n2
    nlinarith [mul_nonneg h1 h2]
  simp only [hill2]
  exact hnum.div hden (fun p hp => ne_of_gt (hdenpos p hp))

/-- Continuity of a two-input Hill response fed by two nonnegative continuous inputs, the composition
form, stated directly (no product-map composition) to keep definitional checking cheap. -/
theorem hill2_comp_continuousOn {X : Type*} [TopologicalSpace X] {D : Set X}
    {a0 a1 a2 a3 K1 K2 n1 n2 : ℝ} (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    {f h : X → ℝ} (hf : ContinuousOn f D) (hh : ContinuousOn h D)
    (hfnn : ∀ x ∈ D, 0 ≤ f x) (hhnn : ∀ x ∈ D, 0 ≤ h x) :
    ContinuousOn (fun x => hill2 a0 a1 a2 a3 K1 K2 n1 n2 (f x) (h x)) D := by
  have hr1 : ContinuousOn (fun x => (f x / K1) ^ n1) D :=
    (hf.div_const K1).rpow_const (fun _ _ => Or.inr hn1)
  have hr2 : ContinuousOn (fun x => (h x / K2) ^ n2) D :=
    (hh.div_const K2).rpow_const (fun _ _ => Or.inr hn2)
  have hnum : ContinuousOn (fun x =>
      a0 + a1 * (f x / K1) ^ n1 + a2 * (h x / K2) ^ n2 + a3 * ((f x / K1) ^ n1 * (h x / K2) ^ n2)) D :=
    ((continuousOn_const.add (continuousOn_const.mul hr1)).add (continuousOn_const.mul hr2)).add
      (continuousOn_const.mul (hr1.mul hr2))
  have hden : ContinuousOn (fun x =>
      1 + (f x / K1) ^ n1 + (h x / K2) ^ n2 + (f x / K1) ^ n1 * (h x / K2) ^ n2) D :=
    ((continuousOn_const.add hr1).add hr2).add (hr1.mul hr2)
  have hdenpos : ∀ x ∈ D,
      (0 : ℝ) < 1 + (f x / K1) ^ n1 + (h x / K2) ^ n2 + (f x / K1) ^ n1 * (h x / K2) ^ n2 := by
    intro x hx
    have h1 : 0 ≤ (f x / K1) ^ n1 := Real.rpow_nonneg (div_nonneg (hfnn x hx) hK1.le) n1
    have h2 : 0 ≤ (h x / K2) ^ n2 := Real.rpow_nonneg (div_nonneg (hhnn x hx) hK2.le) n2
    nlinarith [mul_nonneg h1 h2]
  simp only [hill2]
  exact hnum.div hden (fun x hx => ne_of_gt (hdenpos x hx))

/-- The inducer with the level of one id `s` set to `u`, the rest of `base`. -/
def inducerAt (base : String → ℝ) (s : String) (u : ℝ) : String → ℝ :=
  fun id => if id = s then u else base id

/-- The interpreted valuation, with the chosen inducer's level as a parameter, is continuous in
`(level, state)`. -/
theorem valuation_param_continuous (g : GRN) (base : String → ℝ) (s : String) :
    Continuous (fun v : ℝ × (g.Species → ℝ) =>
      (g.valuation (inducerAt base s v.1) v.2 : String → ℝ)) := by
  refine continuous_pi (fun id => ?_)
  unfold valuation inducerAt
  by_cases h : id ∈ g.regIds
  · simp only [dif_pos h]
    exact (continuous_apply (⟨id, h⟩ : g.Species)).comp continuous_snd
  · simp only [dif_neg h]
    by_cases hs : id = s
    · simp only [if_pos hs]; exact continuous_fst
    · simp only [if_neg hs]; exact continuous_const

/-- Continuity prerequisites for an operator's Hill response: positive dissociation constants and
nonnegative Hill coefficients (per kind). -/
def _root_.Node.Regular (op : Node) : Prop :=
  match op.kind with
  | .receiver | .hill1 => 0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2
  | .hill2 => 0 < (op.rlist "K").getD 0 1 ∧ 0 < (op.rlist "K").getD 1 1 ∧
      0 ≤ (op.rlist "n").getD 0 2 ∧ 0 ≤ (op.rlist "n").getD 1 2
  | .sum => ∀ i, 0 < (op.rlist "K").getD i 1 ∧ 0 ≤ (op.rlist "n").getD i 2
  | _ => True

/-! ## Production is continuous in the inducer level -/

/-- An operator's rate is jointly continuous in the inducer level and the state, on the nonnegative
orthant, for every operator kind. -/
theorem opRate_param_continuousOn (g : GRN) (base : String → ℝ) (s : String) (hbase : ∀ id, 0 ≤ base id)
    (op : Node) (hreg : op.Regular) :
    ContinuousOn (fun v : ℝ × (g.Species → ℝ) =>
      g.opRate (g.valuation (inducerAt base s v.1) v.2) op)
      (Ici 0 ×ˢ univ.pi (fun _ : g.Species => Ici (0 : ℝ))) := by
  have hval : Continuous (fun v : ℝ × (g.Species → ℝ) =>
      (g.valuation (inducerAt base s v.1) v.2 : String → ℝ)) := valuation_param_continuous g base s
  have hvnn : ∀ v ∈ (Ici (0 : ℝ) ×ˢ univ.pi (fun _ : g.Species => Ici (0 : ℝ))),
      ∀ id, 0 ≤ g.valuation (inducerAt base s v.1) v.2 id := by
    intro v hv id
    refine g.valuation_nonneg (fun i => ?_) (fun j => ?_) id
    · unfold inducerAt; by_cases hi : i = s
      · simp only [if_pos hi]; exact mem_Ici.1 (mem_prod.1 hv).1
      · simp only [if_neg hi]; exact hbase i
    · exact mem_Ici.1 ((mem_univ_pi.1 (mem_prod.1 hv).2) j)
  rcases hk : op.kind with _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [opRate, opRateV, hk]
  · exact continuousOn_const
  · exact continuousOn_const
  · exact continuousOn_const
  · exact continuousOn_const
  · simp only [Node.Regular, hk] at hreg
    exact (hill_continuousOn (a0 := (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0)
        (a1 := (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0) hreg.1 hreg.2).comp
      (((continuous_map_headD (g.inputsOf op.id)).comp hval).continuousOn)
      (fun v hv => mem_Ici.2 (headD_map_nonneg' (fun id _ => hvnn v hv id)))
  · simp only [Node.Regular, hk] at hreg
    exact (hill_continuousOn (a0 := (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0)
        (a1 := (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0) hreg.1 hreg.2).comp
      (((continuous_map_headD (g.inputsOf op.id)).comp hval).continuousOn)
      (fun v hv => mem_Ici.2 (headD_map_nonneg' (fun id _ => hvnn v hv id)))
  · simp only [Node.Regular, hk] at hreg
    exact hill2_comp_continuousOn hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2
      (((continuous_map_getD (g.inputsOf op.id) 0).comp hval).continuousOn)
      (((continuous_map_getD (g.inputsOf op.id) 1).comp hval).continuousOn)
      (fun v hv => getD_map_nonneg' (fun id _ => hvnn v hv id) 0)
      (fun v hv => getD_map_nonneg' (fun id _ => hvnn v hv id) 1)
  · simp only [Node.Regular, hk] at hreg
    simp only [List.length_map]
    generalize (List.range (g.inputsOf op.id).length) = R
    induction R with
    | nil => simpa using continuousOn_const
    | cons idx t ih =>
      simp only [List.map_cons, List.sum_cons]
      refine ContinuousOn.add ?_ ih
      exact (hill_continuousOn (a0 := ((op.rnested "alpha").getD idx []).getD 0 0)
          (a1 := ((op.rnested "alpha").getD idx []).getD 1 0) (hreg idx).1 (hreg idx).2).comp
        (((continuous_map_getD (g.inputsOf op.id) idx).comp hval).continuousOn)
        (fun v hv => mem_Ici.2 (getD_map_nonneg' (fun id _ => hvnn v hv id) idx))

/-- A sum of operator rates over a list of `Regular` operators is jointly continuous. -/
theorem continuousOn_opSum (g : GRN) (base : String → ℝ) (s : String) (hbase : ∀ id, 0 ≤ base id)
    (L : List Node) : (∀ op ∈ L, op.Regular) →
    ContinuousOn (fun v : ℝ × (g.Species → ℝ) =>
      (L.map (g.opRate (g.valuation (inducerAt base s v.1) v.2))).sum)
      (Ici 0 ×ˢ univ.pi (fun _ : g.Species => Ici (0 : ℝ))) := by
  induction L with
  | nil => intro _; simpa using continuousOn_const
  | cons a t ih =>
    intro hL
    simp only [List.map_cons, List.sum_cons]
    refine ContinuousOn.add ?_ ?_
    · exact opRate_param_continuousOn g base s hbase a (hL a List.mem_cons_self)
    · exact ih (fun op hop => hL op (List.mem_cons_of_mem a hop))

/-- **The interpreted production is jointly continuous in the inducer level and the state** on the
nonnegative orthant, for any acyclic well-formed GRN whose operators are `Regular`. -/
theorem prodOf_param_continuousOn (g : GRN) (base : String → ℝ) (s : String) (hbase : ∀ id, 0 ≤ base id)
    (hreg : ∀ op ∈ g.operators, op.Regular) (i : g.Species) :
    ContinuousOn (fun v : ℝ × (g.Species → ℝ) => g.prodOf (inducerAt base s v.1) i v.2)
      (Ici 0 ×ˢ univ.pi (fun _ : g.Species => Ici (0 : ℝ))) := by
  unfold prodOf
  exact continuousOn_opSum g base s hbase _ (fun op hop => hreg op (List.mem_of_mem_filter hop))

/-! ## General-GRN EC50 through the functor's steady state -/

/-- A well-posed GRN with the level of one inducer `s` reset to a nonnegative `u`. -/
def _root_.GRN.WellPosed.setInducer {g : GRN} (wp : g.WellPosed) (s : String) (u : ℝ) (hu : 0 ≤ u) :
    g.WellPosed :=
  { wp with
    inducer := inducerAt wp.inducer s u
    inducer_nonneg := fun id => by
      unfold inducerAt; split
      · exact hu
      · exact wp.inducer_nonneg id }

/-- **General-GRN EC50 through the real `steadyPoint`.** For an acyclic, well-posed GRN whose operators are
`Regular`, if the reporter's steady level is strictly monotone in a chosen inducer's level on `[lo, hi]`,
then it has a unique EC50. Continuity is discharged automatically (`prodOf_param_continuousOn` +
`steadyFam_continuousOn`); strict monotonicity, which depends on the drive from inducer to reporter, is
the one hypothesis, dischargeable via the `steadyFam_lt_base` / `steadyFam_lt_step` engine. -/
theorem grn_reporter_ec50 (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed) (s : String) (top : g.Species)
    (hreg : ∀ op ∈ g.operators, op.Regular) {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    (hstrict : StrictMonoOn (fun u => steadyFam (g.regulates_wf hac) wp.γ
      (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u top) (Set.Icc lo hi))
    {L : ℝ} (hL : L ∈ Set.Icc
      (steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) lo top)
      (steadyFam (g.regulates_wf hac) wp.γ (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) hi top)) :
    ∃! u, u ∈ Set.Icc lo hi ∧
      steadyFam (g.regulates_wf hac) wp.γ
        (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u top = L := by
  have hcont : ContinuousOn (fun u => steadyFam (g.regulates_wf hac) wp.γ
      (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u top) (Set.Icc lo hi) := by
    refine (steadyFam_continuousOn (g.regulates_wf hac) wp.γ wp.γ_pos
      (fun t ht k x hx => ?_) (fun i => ?_) top).mono (fun u hu => mem_Ici.2 (le_trans hlo hu.1))
    · exact g.prodOf_nonneg (wp.setInducer s t (mem_Ici.1 ht)) k x hx
    · exact prodOf_param_continuousOn g wp.inducer s wp.inducer_nonneg hreg i
  exact steadyFam_ec50 (g.regulates_wf hac) wp.γ
    (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) top hle hcont hstrict hL

/-! ## `MonoActivating` from graph sign data -/

/-- **`MonoActivating` from the interaction graph.** For a well-posed GRN whose operators are `Regular`,
carry no `sum`, and whose per-port interaction-graph signs are all `+1` (pure activation), every operator
is `MonoActivating`. This discharges the per-operator hypotheses of `grn_reporter_ec50` and
`grn_doseResponse_mono` directly from the graph, with no hand-supplied kinetic inequalities. -/
theorem monoActivating_of_graph (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular)
    (hnosum : ∀ op ∈ g.operators, op.kind ≠ NodeKind.sum)
    (hsign : ∀ op ∈ g.operators, ∀ sgn ∈ operatorInputSigns op, sgn = some (1 : Int))
    (op : Node) (hop : op ∈ g.operators) : op.MonoActivating := by
  have hS := hsign op hop
  have pairSign_lt : ∀ {a b : ℚ}, pairSign a b = some 1 → a < b := by
    intro a b h
    simp only [pairSign] at h
    split_ifs at h with h1 h2 <;> first | exact h1 | simp_all
  have sign_le : ∀ {pairs : List (ℚ × ℚ)}, signFromPairs pairs = some 1 →
      ∀ p ∈ pairs, p.1 ≤ p.2 := by
    intro pairs h p hp
    by_contra hc
    rw [not_le] at hc
    have hneg : pairs.any (fun q => decide (q.2 < q.1)) = true :=
      List.any_eq_true.2 ⟨p, hp, by simpa using hc⟩
    simp only [signFromPairs, hneg, Bool.and_true] at h
    split_ifs at h <;> simp_all
  rcases hk : op.kind with _ | _ | _ | _ | _ | _ | _ | _
  · simp only [Node.MonoActivating, hk]
  · simp only [Node.MonoActivating, hk]
  · simp only [Node.MonoActivating, hk]
  · simp only [Node.MonoActivating, hk]
  · -- receiver
    have hRr := hreg op hop
    simp only [Node.Regular, hk] at hRr
    simp only [Node.MonoActivating, hk]
    refine ⟨hRr.1, hRr.2, ?_⟩
    rcases halpha : op.alphaNums with _ | ⟨a0, _ | ⟨a1, rest⟩⟩
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · have hps := hS (pairSign a0 a1) (by simp [operatorInputSigns, hk, halpha])
      show (a0 : ℝ) ≤ (a1 : ℝ)
      exact_mod_cast (pairSign_lt hps).le
  · -- hill1
    have hRr := hreg op hop
    simp only [Node.Regular, hk] at hRr
    simp only [Node.MonoActivating, hk]
    refine ⟨hRr.1, hRr.2, ?_⟩
    rcases halpha : op.alphaNums with _ | ⟨a0, _ | ⟨a1, rest⟩⟩
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · have hps := hS (pairSign a0 a1) (by simp [operatorInputSigns, hk, halpha])
      show (a0 : ℝ) ≤ (a1 : ℝ)
      exact_mod_cast (pairSign_lt hps).le
  · -- hill2
    have hRr := hreg op hop
    simp only [Node.Regular, hk] at hRr
    simp only [Node.MonoActivating, hk]
    rcases halpha : op.alphaNums with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩⟩
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · exact absurd (hS none (by simp [operatorInputSigns, hk, halpha])) (by simp)
    · have h1 := hS (signFromPairs [(a0, a1), (a2, a3)]) (by simp [operatorInputSigns, hk, halpha])
      have h2 := hS (signFromPairs [(a0, a2), (a1, a3)]) (by simp [operatorInputSigns, hk, halpha])
      have e1 : a0 ≤ a1 := sign_le h1 (a0, a1) (by simp)
      have e2 : a2 ≤ a3 := sign_le h1 (a2, a3) (by simp)
      have e3 : a0 ≤ a2 := sign_le h2 (a0, a2) (by simp)
      have e4 : a1 ≤ a3 := sign_le h2 (a1, a3) (by simp)
      refine ⟨hRr.1, hRr.2.1, hRr.2.2.1, hRr.2.2.2, ?_, ?_, ?_, ?_⟩
      · show (a0 : ℝ) ≤ (a1 : ℝ); exact_mod_cast e1
      · show (a2 : ℝ) ≤ (a3 : ℝ); exact_mod_cast e2
      · show (a0 : ℝ) ≤ (a2 : ℝ); exact_mod_cast e3
      · show (a1 : ℝ) ≤ (a3 : ℝ); exact_mod_cast e4
  · -- sum
    exact absurd hk (hnosum op hop)

end GRN
