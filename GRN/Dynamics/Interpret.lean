import Mathlib
import GRN.InteractionGraph
import GRN.Dynamics.Feedforward
import GRN.Dynamics.VectorField
import GRN.Dynamics.Sensor

/-!
# Phase B — interpreting a GRN into a `FeedforwardSystem`

The functor `GRN → FeedforwardSystem`. Structural half: the regulated-species carrier, the "regulates"
relation, and its well-foundedness from acyclicity. Kinetics half: the operator-interpretation
definitions (`valuation`, `opRate`, `prodOf`) that build the production function. The `local'`/`nonneg`
obligations and the `FeedforwardSystem` assembly build on these.

Scope: single-input operators (`source`, `receiver`, `hill1`) — the inducible-cascade sensor class;
two-input logic (`hill2`, `sum`) contributes `0` here and is a refinement.
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

/-- An operator's expression rate as a function of its input values (in port order). Single-input
Hill/receiver operators use the Hill response; a source is a constant; other kinds contribute `0`. -/
noncomputable def opRateV (op : Node) (vals : List ℝ) : ℝ :=
  match op.kind with
  | .source => op.rparam "rate" 0
  | .receiver | .hill1 =>
      hill ((op.alphaNums.map (fun q => (q : ℝ))).getD 0 0)
        ((op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
        (op.rparam "K" 1) (op.rparam "n" 2) (vals.headD 0)
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
nonnegative Hill parameters / rates on every operator. -/
structure WellPosed (g : GRN) where
  inducer : String → ℝ
  inducer_nonneg : ∀ id, 0 ≤ inducer id
  γ : g.Species → ℝ
  γ_pos : ∀ i, 0 < γ i
  rate_nonneg : ∀ op ∈ g.operators, 0 ≤ op.rparam "rate" 0
  K_pos : ∀ op ∈ g.operators, 0 < op.rparam "K" 1
  a0_nonneg : ∀ op ∈ g.operators, 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0
  a1_nonneg : ∀ op ∈ g.operators, 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0

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
  have hvals : 0 ≤ ((g.inputsOf op.id).map (g.valuation wp.inducer x)).headD 0 :=
    map_headD_nonneg (g.valuation_nonneg wp.inducer_nonneg hx) _
  unfold opRate opRateV
  split <;>
    first
      | exact wp.rate_nonneg op hmem
      | exact hill_nonneg (wp.K_pos op hmem) (wp.a0_nonneg op hmem) (wp.a1_nonneg op hmem) _ hvals
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

/-- An activating operator's rate is monotone in its input values. -/
theorem opRate_mono (g : GRN) (op : Node) {val₁ val₂ : String → ℝ}
    (hK : 0 < op.rparam "K" 1) (hn : 0 ≤ op.rparam "n" 2)
    (hact : (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
    (h01 : ∀ id ∈ g.inputsOf op.id, 0 ≤ val₁ id)
    (hle : ∀ id ∈ g.inputsOf op.id, val₁ id ≤ val₂ id) :
    g.opRate val₁ op ≤ g.opRate val₂ op := by
  unfold opRate opRateV
  split <;>
    first
      | exact le_refl _
      | exact (hill_monotoneOn hK hn hact)
          (Set.mem_Ici.mpr (headD_map_nonneg' h01))
          (Set.mem_Ici.mpr (headD_map_nonneg' (fun id hid => (h01 id hid).trans (hle id hid))))
          (headD_map_mono hle)

/-- **Monotone dose-response through the functor** (activating case). Raising the inducer levels of an
acyclic, well-posed GRN whose operators are all activating does not decrease any species' steady state —
so the reporter's dose-response is monotone. Obtained by instantiating `steady_le` on the interpreted
production. -/
theorem grn_doseResponse_mono (g : GRN) (hac : g.Acyclic) (wp wp' : g.WellPosed)
    (hγ : ∀ i, wp.γ i = wp'.γ i) (hind : ∀ id, wp.inducer id ≤ wp'.inducer id)
    (hn : ∀ op ∈ g.operators, 0 ≤ op.rparam "n" 2)
    (hact : ∀ op ∈ g.operators,
      (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0) :
    ∀ i, (g.toSystem hac wp).steadyPoint i ≤ (g.toSystem hac wp').steadyPoint i := by
  apply Dynamics.FeedforwardSystem.steady_le _ _ hγ
  · -- hmonoT: T = toSystem wp' is monotone in earlier species
    intro i x y hx _ hxy
    refine List.sum_le_sum (fun op hop => ?_)
    have hmem : op ∈ g.operators := List.mem_of_mem_filter hop
    refine g.opRate_mono op (wp'.K_pos op hmem) (hn op hmem) (hact op hmem)
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
    refine g.opRate_mono op (wp'.K_pos op hmem) (hn op hmem) (hact op hmem)
      (fun id _ => g.valuation_nonneg wp.inducer_nonneg hx id) (fun id _ => ?_)
    unfold valuation
    split
    · exact le_refl _
    · exact hind _

end GRN
