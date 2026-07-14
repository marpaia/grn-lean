import Mathlib
import GRN.InteractionGraph
import GRN.Dynamics.Feedforward
import GRN.Dynamics.VectorField
import GRN.Dynamics.Sensor

/-!
# Interpreting a GRN into a `FeedforwardSystem`

The functor `GRN → FeedforwardSystem`. Structural half: the regulated-species carrier, the "regulates"
relation, and its well-foundedness from acyclicity. Kinetics half: the operator-interpretation
definitions (`valuation`, `opRate`, `prodOf`) that build the production function. The `local'`/`nonneg`
obligations and the `FeedforwardSystem` assembly build on these.

Scope: all five operators (`source`, `receiver`, `hill1`, `hill2`, `sum`) are interpreted with their LOICA
kinetics, so uniqueness (`grn_unique_steady`) covers every kind. Dose-response monotonicity
(`grn_doseResponse_mono`) covers `source`/`receiver`/`hill1`/`hill2` (the `MonoActivating` predicate);
`sum`'s per-input dose-response is not covered by `MonoActivating`.
-/

namespace GRN

open Dynamics (hill hill_nonneg hill_monotoneOn)

/-- Ids of the regulated species (regulators and reporters); supplements are external inducers, not
state coordinates. -/
def regIds (g : GRN) : Finset String :=
  ((g.nodes.filter (fun n => decide (n.kind = .regulator ∨ n.kind = .reporter))).map (·.id)).toFinset

/-- The regulated-species carrier — the state coordinates of the assembled ODE. -/
abbrev Species (g : GRN) : Type := {s : String // s ∈ g.regIds}

/-- `j` directly regulates `i`: `j` is an input to an operator that produces `i`. -/
def regulates (g : GRN) (j i : g.Species) : Prop :=
  ∃ op ∈ g.operators, (j : String) ∈ g.inputsOf op.id ∧ (i : String) ∈ g.outputsOf op.id

/-- Acyclicity: no species transitively regulates itself. -/
def Acyclic (g : GRN) : Prop := ∀ i : g.Species, ¬ Relation.TransGen g.regulates i i

/-- The regulation relation is well-founded when the circuit is acyclic — the hypothesis a sensor GRN
supplies to the `FeedforwardSystem` IR. -/
theorem regulates_wf (g : GRN) (h : g.Acyclic) : WellFounded g.regulates :=
  Dynamics.wellFounded_of_acyclic h

/-- A GRN with no regulation edges (e.g. only source-driven species) is acyclic. -/
theorem acyclic_of_no_regulates (g : GRN) (h : ∀ j i, ¬ g.regulates j i) : g.Acyclic := by
  have key : ∀ a b, Relation.TransGen g.regulates a b → False := by
    intro a b hab
    induction hab with
    | single hr => exact h _ _ hr
    | tail _ hr _ => exact h _ _ hr
  exact fun i htg => key i i htg

/-! ## Kinetics: operator interpretation -/

/-- A scalar real-valued parameter of a node (default `d` if absent or non-scalar). -/
def _root_.Node.rparam (n : Node) (key : String) (d : ℝ) : ℝ :=
  match n.param? key with
  | some (.num q) => (q : ℝ)
  | _ => d

/-- The value fed to an input id: the state coordinate if it is a regulated species, else the external
inducer level. -/
noncomputable def valuation (g : GRN) (inducer : String → ℝ) (x : g.Species → ℝ) (id : String) : ℝ :=
  if h : id ∈ g.regIds then x ⟨id, h⟩ else inducer id

/-- A list-valued real parameter of a node (for the two-input operators' `K`/`n`). -/
def _root_.Node.rlist (nd : Node) (key : String) : List ℝ :=
  (((nd.param? key).map ParamValue.numList).getD []).map (fun q => (q : ℝ))

/-- A nested-list real parameter (for the `sum` operator's per-input `alpha` pairs). -/
def _root_.Node.rnested (nd : Node) (key : String) : List (List ℝ) :=
  match nd.param? key with
  | some (.list xs) => xs.map (fun p => p.numList.map (fun q => (q : ℝ)))
  | _ => []

/-- The two-input Hill response (LOICA `Hill2`). -/
noncomputable def hill2 (a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 : ℝ) : ℝ :=
  (a0 + a1 * (u1 / K1) ^ n1 + a2 * (u2 / K2) ^ n2 + a3 * ((u1 / K1) ^ n1 * (u2 / K2) ^ n2)) /
    (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2)

theorem hill2_nonneg {a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) :
    0 ≤ hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 := by
  unfold hill2
  have hr1 : 0 ≤ (u1 / K1) ^ n1 := Real.rpow_nonneg (div_nonneg hu1 hK1.le) n1
  have hr2 : 0 ≤ (u2 / K2) ^ n2 := Real.rpow_nonneg (div_nonneg hu2 hK2.le) n2
  apply div_nonneg
  · nlinarith [mul_nonneg ha1 hr1, mul_nonneg ha2 hr2, mul_nonneg ha3 (mul_nonneg hr1 hr2)]
  · nlinarith [mul_nonneg hr1 hr2]

/-- The two-input Hill response is monotone in its first input when it activates in both contexts
(`a0 ≤ a1` and `a2 ≤ a3`). -/
theorem hill2_monotoneOn_left {a0 a1 a2 a3 K1 K2 n1 n2 u2 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 ≤ n1) (hu2 : 0 ≤ u2)
    (ha : a0 ≤ a1) (ha' : a2 ≤ a3) :
    MonotoneOn (fun u1 => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  simp only [hill2]
  set r2 := (u2 / K2) ^ n2
  set ru := (u / K1) ^ n1
  set rv := (v / K1) ^ n1
  have hr2 : 0 ≤ r2 := Real.rpow_nonneg (div_nonneg hu2 hK2.le) n2
  have hru : 0 ≤ ru := Real.rpow_nonneg (div_nonneg hu hK1.le) n1
  have hrle : ru ≤ rv := by
    apply Real.rpow_le_rpow (div_nonneg hu hK1.le) _ hn1
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right huv (inv_pos.2 hK1).le
  have hdu : (0:ℝ) < 1 + ru + r2 + ru * r2 := by nlinarith [mul_nonneg hru hr2]
  have hrv : 0 ≤ rv := le_trans hru hrle
  have hdv : (0:ℝ) < 1 + rv + r2 + rv * r2 := by nlinarith [mul_nonneg hrv hr2]
  rw [← sub_nonneg, div_sub_div _ _ (ne_of_gt hdv) (ne_of_gt hdu)]
  apply div_nonneg
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle)) hr2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr2) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr2) hr2) (sub_nonneg.2 hrle)]
  · exact (mul_pos hdv hdu).le

/-- The two-input Hill response is monotone in its second input when it activates in both contexts
(`a0 ≤ a2` and `a1 ≤ a3`). -/
theorem hill2_monotoneOn_right {a0 a1 a2 a3 K1 K2 n1 n2 u1 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn2 : 0 ≤ n2) (hu1 : 0 ≤ u1)
    (ha : a0 ≤ a2) (ha' : a1 ≤ a3) :
    MonotoneOn (fun u2 => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  simp only [hill2]
  set r1 := (u1 / K1) ^ n1
  set ru := (u / K2) ^ n2
  set rv := (v / K2) ^ n2
  have hr1 : 0 ≤ r1 := Real.rpow_nonneg (div_nonneg hu1 hK1.le) n1
  have hru : 0 ≤ ru := Real.rpow_nonneg (div_nonneg hu hK2.le) n2
  have hrle : ru ≤ rv := by
    apply Real.rpow_le_rpow (div_nonneg hu hK2.le) _ hn2
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right huv (inv_pos.2 hK2).le
  have hrv : 0 ≤ rv := le_trans hru hrle
  have hdu : (0:ℝ) < 1 + r1 + ru + r1 * ru := by nlinarith [mul_nonneg hr1 hru]
  have hdv : (0:ℝ) < 1 + r1 + rv + r1 * rv := by nlinarith [mul_nonneg hr1 hrv]
  rw [← sub_nonneg, div_sub_div _ _ (ne_of_gt hdv) (ne_of_gt hdu)]
  apply div_nonneg
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle)) hr1,
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr1) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr1) hr1) (sub_nonneg.2 hrle)]
  · exact (mul_pos hdv hdu).le

/-- The two-input Hill response is jointly monotone when it activates in every context — raising either
input does not decrease the output. -/
theorem hill2_mono {a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 u1' u2' : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2)
    (h01 : a0 ≤ a1) (h23 : a2 ≤ a3) (h02 : a0 ≤ a2) (h13 : a1 ≤ a3)
    (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hu1' : u1 ≤ u1') (hu2' : u2 ≤ u2') :
    hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 ≤ hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1' u2' :=
  calc hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2
      ≤ hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1' u2 :=
        hill2_monotoneOn_left hK1 hK2 hn1 hu2 h01 h23
          (Set.mem_Ici.mpr hu1) (Set.mem_Ici.mpr (le_trans hu1 hu1')) hu1'
    _ ≤ hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1' u2' :=
        hill2_monotoneOn_right hK1 hK2 hn2 (le_trans hu1 hu1') h02 h13
          (Set.mem_Ici.mpr hu2) (Set.mem_Ici.mpr (le_trans hu2 hu2')) hu2'

theorem getD_map_nonneg {f : String → ℝ} (hf : ∀ id, 0 ≤ f id) (l : List String) (k : ℕ) :
    0 ≤ (l.map f).getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    cases k with
    | zero => simpa using hf a
    | succ k => simpa using ih k

/-- An operator's expression rate as a function of its input values (in port order). Single-input
Hill/receiver operators use the Hill response, `hill2` the two-input response, a source a constant;
other kinds contribute `0`. -/
noncomputable def opRateV (op : Node) (vals : List ℝ) : ℝ :=
  match op.kind with
  | .source => op.rparam "rate" 0
  | .receiver | .hill1 =>
      hill ((op.alphaNums.map (fun q => (q : ℝ))).getD 0 0)
        ((op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
        (op.rparam "K" 1) (op.rparam "n" 2) (vals.headD 0)
  | .hill2 =>
      hill2 ((op.alphaNums.map (fun q => (q : ℝ))).getD 0 0)
        ((op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
        ((op.alphaNums.map (fun q => (q : ℝ))).getD 2 0)
        ((op.alphaNums.map (fun q => (q : ℝ))).getD 3 0)
        ((op.rlist "K").getD 0 1) ((op.rlist "K").getD 1 1)
        ((op.rlist "n").getD 0 2) ((op.rlist "n").getD 1 2)
        (vals.getD 0 0) (vals.getD 1 0)
  | .sum =>
      ((List.range vals.length).map (fun i =>
        hill (((op.rnested "alpha").getD i []).getD 0 0) (((op.rnested "alpha").getD i []).getD 1 0)
          ((op.rlist "K").getD i 1) ((op.rlist "n").getD i 2) (vals.getD i 0))).sum
  | _ => 0

/-- An operator's expression rate, reading input ids through a valuation. -/
noncomputable def opRate (g : GRN) (val : String → ℝ) (op : Node) : ℝ :=
  opRateV op ((g.inputsOf op.id).map val)

/-- The production rate of species `i`: the sum over operators producing `i` of their expression rates. -/
noncomputable def prodOf (g : GRN) (inducer : String → ℝ) (i : g.Species) (x : g.Species → ℝ) : ℝ :=
  ((g.operators.filter (fun op => decide ((i : String) ∈ g.outputsOf op.id))).map
    (g.opRate (g.valuation inducer x))).sum

/-- `valuation` is nonnegative on nonnegative states and inducers. -/
theorem valuation_nonneg (g : GRN) {inducer : String → ℝ} {x : g.Species → ℝ}
    (hind : ∀ id, 0 ≤ inducer id) (hx : ∀ j, 0 ≤ x j) (id : String) :
    0 ≤ g.valuation inducer x id := by
  unfold valuation
  split
  · exact hx _
  · exact hind _

theorem map_headD_nonneg {f : String → ℝ} (hf : ∀ id, 0 ≤ f id) (l : List String) :
    0 ≤ (l.map f).headD 0 := by
  cases l with
  | nil => simp
  | cons a _ => simpa using hf a

/-! ## Well-posedness and the assembled system -/

/-- The data making a GRN's assembled ODE well-posed: nonnegative inducers, positive degradation, and
nonnegative Hill parameters / rates on every operator. A `sum` operator combines activating Hill
summands (`a0 ≤ a1` per input), matching the `+1` sign every `sum` port carries in the interaction
graph. The `alpha` vector of each single- or two-input Hill operator carries its full complement of
levels (two for `receiver`/`hill1`, four for `hill2`), so the interaction-graph sign extraction reads
the same coefficients the kinetics use. -/
structure WellPosed (g : GRN) where
  inducer : String → ℝ
  inducer_nonneg : ∀ id, 0 ≤ inducer id
  γ : g.Species → ℝ
  γ_pos : ∀ i, 0 < γ i
  rate_nonneg : ∀ op ∈ g.operators, 0 ≤ op.rparam "rate" 0
  K_pos : ∀ op ∈ g.operators, 0 < op.rparam "K" 1
  a0_nonneg : ∀ op ∈ g.operators, 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0
  a1_nonneg : ∀ op ∈ g.operators, 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0
  a2_nonneg : ∀ op ∈ g.operators, 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 2 0
  a3_nonneg : ∀ op ∈ g.operators, 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 3 0
  K1_pos : ∀ op ∈ g.operators, 0 < (op.rlist "K").getD 0 1
  K2_pos : ∀ op ∈ g.operators, 0 < (op.rlist "K").getD 1 1
  sum_wp : ∀ op ∈ g.operators, ∀ i,
    0 ≤ ((op.rnested "alpha").getD i []).getD 0 0 ∧
    0 ≤ ((op.rnested "alpha").getD i []).getD 1 0 ∧
    0 < (op.rlist "K").getD i 1 ∧
    ((op.rnested "alpha").getD i []).getD 0 0 ≤ ((op.rnested "alpha").getD i []).getD 1 0
  alpha_wf : ∀ op ∈ g.operators,
    ((op.kind = .receiver ∨ op.kind = .hill1) → 2 ≤ op.alphaNums.length) ∧
    (op.kind = .hill2 → 4 ≤ op.alphaNums.length)

/-- Production reads only direct regulators — the `local'` obligation. -/
theorem prodOf_local (g : GRN) (inducer : String → ℝ) (i : g.Species) (x y : g.Species → ℝ)
    (hxy : ∀ j, g.regulates j i → x j = y j) :
    g.prodOf inducer i x = g.prodOf inducer i y := by
  unfold prodOf
  refine congrArg List.sum (List.map_congr_left (fun op hop => ?_))
  unfold opRate
  refine congrArg (opRateV op) (List.map_congr_left (fun id hid => ?_))
  unfold valuation
  split
  · rename_i hmem
    exact hxy ⟨id, hmem⟩ ⟨op, List.mem_of_mem_filter hop, hid, by
      have := List.of_mem_filter hop; simpa using this⟩
  · rfl

/-- Production is nonnegative on nonnegative states — the `nonneg` obligation. -/
theorem prodOf_nonneg (g : GRN) (wp : g.WellPosed) (i : g.Species) (x : g.Species → ℝ)
    (hx : ∀ j, 0 ≤ x j) : 0 ≤ g.prodOf wp.inducer i x := by
  unfold prodOf
  refine List.sum_nonneg (fun v hv => ?_)
  simp only [List.mem_map] at hv
  obtain ⟨op, hop, rfl⟩ := hv
  have hmem : op ∈ g.operators := List.mem_of_mem_filter hop
  have hvnn : ∀ id, 0 ≤ g.valuation wp.inducer x id := g.valuation_nonneg wp.inducer_nonneg hx
  have hvals : 0 ≤ ((g.inputsOf op.id).map (g.valuation wp.inducer x)).headD 0 :=
    map_headD_nonneg hvnn _
  have hv0 : 0 ≤ ((g.inputsOf op.id).map (g.valuation wp.inducer x)).getD 0 0 :=
    getD_map_nonneg hvnn _ 0
  have hv1 : 0 ≤ ((g.inputsOf op.id).map (g.valuation wp.inducer x)).getD 1 0 :=
    getD_map_nonneg hvnn _ 1
  unfold opRate opRateV
  split <;>
    first
      | exact wp.rate_nonneg op hmem
      | exact hill_nonneg (wp.K_pos op hmem) (wp.a0_nonneg op hmem) (wp.a1_nonneg op hmem) _ hvals
      | exact hill2_nonneg (wp.a0_nonneg op hmem) (wp.a1_nonneg op hmem) (wp.a2_nonneg op hmem)
          (wp.a3_nonneg op hmem) (wp.K1_pos op hmem) (wp.K2_pos op hmem) hv0 hv1
      | refine List.sum_nonneg (fun v hv => ?_)
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
        exact hill_nonneg (wp.sum_wp op hmem i).2.2.1 (wp.sum_wp op hmem i).1
          (wp.sum_wp op hmem i).2.1 _ (getD_map_nonneg hvnn _ i)
      | exact le_refl 0

/-- The assembled feedforward system of an acyclic, well-posed GRN. -/
noncomputable def toSystem (g : GRN) (h : g.Acyclic) (wp : g.WellPosed) :
    Dynamics.FeedforwardSystem g.Species g.regulates where
  wf := g.regulates_wf h
  γ := wp.γ
  hγ := wp.γ_pos
  prod := g.prodOf wp.inducer
  local' := g.prodOf_local wp.inducer
  nonneg := g.prodOf_nonneg wp

/-- **The functor's payoff: an acyclic, well-posed GRN has a unique steady state** — obtained end to end
from the `GRN` datatype through the interpretation and the constructive IR. -/
theorem grn_unique_steady (g : GRN) (h : g.Acyclic) (wp : g.WellPosed) :
    ∃! x, (g.toSystem h wp).IsSteady x :=
  (g.toSystem h wp).exists_unique_steady

/-! ## Dose-response monotonicity (activating case) -/

theorem headD_map_nonneg' {f : String → ℝ} {l : List String} (h : ∀ id ∈ l, 0 ≤ f id) :
    0 ≤ (l.map f).headD 0 := by
  cases l with
  | nil => simp
  | cons a _ => simpa using h a (by simp)

theorem headD_map_mono {f₁ f₂ : String → ℝ} {l : List String} (h : ∀ id ∈ l, f₁ id ≤ f₂ id) :
    (l.map f₁).headD 0 ≤ (l.map f₂).headD 0 := by
  cases l with
  | nil => simp
  | cons a _ => simpa using h a (by simp)

theorem getD_map_nonneg' {f : String → ℝ} {l : List String} (h : ∀ id ∈ l, 0 ≤ f id) (k : ℕ) :
    0 ≤ (l.map f).getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    cases k with
    | zero => simpa using h a (by simp)
    | succ k => simpa using ih (fun id hid => h id (by simp [hid])) k

theorem getD_map_mono {f₁ f₂ : String → ℝ} {l : List String} (h : ∀ id ∈ l, f₁ id ≤ f₂ id) (k : ℕ) :
    (l.map f₁).getD k 0 ≤ (l.map f₂).getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    cases k with
    | zero => simpa using h a (by simp)
    | succ k => simpa using ih (fun id hid => h id (by simp [hid])) k

/-- The per-operator condition under which its rate is monotone in its inputs: an activating Hill/receiver,
or a `hill2` activating in every context. -/
def _root_.Node.MonoActivating (op : Node) : Prop :=
  match op.kind with
  | .receiver | .hill1 =>
      0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0
  | .hill2 =>
      0 < (op.rlist "K").getD 0 1 ∧ 0 < (op.rlist "K").getD 1 1 ∧
      0 ≤ (op.rlist "n").getD 0 2 ∧ 0 ≤ (op.rlist "n").getD 1 2 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 2 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 3 0 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 2 0 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 3 0
  | .sum => False
  | _ => True

/-- An activating operator's rate is monotone in its input values (covers single-input Hill/receiver and
two-input `hill2`). -/
theorem opRate_mono (g : GRN) (op : Node) {val₁ val₂ : String → ℝ}
    (hact : op.MonoActivating)
    (h01 : ∀ id ∈ g.inputsOf op.id, 0 ≤ val₁ id)
    (hle : ∀ id ∈ g.inputsOf op.id, val₁ id ≤ val₂ id) :
    g.opRate val₁ op ≤ g.opRate val₂ op := by
  have hillCase : ∀ (hh : 0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0),
      hill ((op.alphaNums.map (fun q => (q : ℝ))).getD 0 0) ((op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
          (op.rparam "K" 1) (op.rparam "n" 2) ((g.inputsOf op.id |>.map val₁).headD 0) ≤
        hill ((op.alphaNums.map (fun q => (q : ℝ))).getD 0 0) ((op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
          (op.rparam "K" 1) (op.rparam "n" 2) ((g.inputsOf op.id |>.map val₂).headD 0) :=
    fun hh => hill_monotoneOn hh.1 hh.2.1 hh.2.2
      (Set.mem_Ici.mpr (headD_map_nonneg' h01))
      (Set.mem_Ici.mpr (headD_map_nonneg' (fun id hid => (h01 id hid).trans (hle id hid))))
      (headD_map_mono hle)
  rcases hk : op.kind with _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [opRate, opRateV, Node.MonoActivating, hk] at hact ⊢
  · exact le_refl _
  · exact le_refl _
  · exact le_refl _
  · exact le_refl _
  · exact hillCase hact
  · exact hillCase hact
  · exact hill2_mono hact.1 hact.2.1 hact.2.2.1 hact.2.2.2.1 hact.2.2.2.2.1
      hact.2.2.2.2.2.1 hact.2.2.2.2.2.2.1 hact.2.2.2.2.2.2.2
      (getD_map_nonneg' h01 0) (getD_map_nonneg' h01 1) (getD_map_mono hle 0) (getD_map_mono hle 1)

/-- **Monotone dose-response through the functor** (activating case). Raising the inducer levels of an
acyclic, well-posed GRN whose operators are all activating does not decrease any species' steady state —
so the reporter's dose-response is monotone. Obtained by instantiating `steady_le` on the interpreted
production. -/
theorem grn_doseResponse_mono (g : GRN) (hac : g.Acyclic) (wp wp' : g.WellPosed)
    (hγ : ∀ i, wp.γ i = wp'.γ i) (hind : ∀ id, wp.inducer id ≤ wp'.inducer id)
    (hMA : ∀ op ∈ g.operators, op.MonoActivating) :
    ∀ i, (g.toSystem hac wp).steadyPoint i ≤ (g.toSystem hac wp').steadyPoint i := by
  apply Dynamics.FeedforwardSystem.steady_le _ _ hγ
  · -- hmonoT: T = toSystem wp' is monotone in earlier species
    intro i x y hx _ hxy
    refine List.sum_le_sum (fun op hop => ?_)
    have hmem : op ∈ g.operators := List.mem_of_mem_filter hop
    refine g.opRate_mono op (hMA op hmem)
      (fun id _ => g.valuation_nonneg wp'.inducer_nonneg hx id) (fun id hid => ?_)
    unfold valuation
    split
    · rename_i hmemid
      exact hxy ⟨id, hmemid⟩ ⟨op, hmem, hid, by have := List.of_mem_filter hop; simpa using this⟩
    · exact le_refl _
  · -- hdom: raising the inducer dominates
    intro i x hx
    refine List.sum_le_sum (fun op hop => ?_)
    have hmem : op ∈ g.operators := List.mem_of_mem_filter hop
    refine g.opRate_mono op (hMA op hmem)
      (fun id _ => g.valuation_nonneg wp.inducer_nonneg hx id) (fun id _ => ?_)
    unfold valuation
    split
    · exact le_refl _
    · exact hind _

/-- **End-to-end composition.** The interpretation and the constructive machinery compose: any GRN with no
regulation edges (a constitutive / source-driven sensor) is acyclic, so the functor delivers a unique
steady state. A fully concrete `GRN` *value* additionally needs `DecidableEq` computation on `Node`. -/
example (g : GRN) (hnr : ∀ j i, ¬ g.regulates j i) (wp : g.WellPosed) :
    ∃! x, (g.toSystem (g.acyclic_of_no_regulates hnr) wp).IsSteady x :=
  g.grn_unique_steady (g.acyclic_of_no_regulates hnr) wp

end GRN
