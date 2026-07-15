import Mathlib
import GRN.Dynamics.Reachability
import GRN.Dynamics.TopoOrder

/-!
# A worked reachability example: a two-stage activating cascade

A concrete all-activating cascade `IPTG → Rc → TF → P → GFP`: an inducer `IPTG` drives a receiver `Rc`
producing the regulator `TF`, which drives an activating Hill promoter `P` producing the reporter `GFP`.
Both operators are strictly-activating single-input Hill responses, so there is a strict monotone path
from `IPTG` to `GFP`, and the reporter's dose-response has a unique EC50, obtained by feeding the path
witness to `grn_reporter_ec50_of_strictPath`.
-/

namespace GRN.ReachExample

open GRN GRN.Dynamics

/-- An activating receiver, `alpha = [0, 100]`. -/
def rcv : Node := { id := "Rc", kind := .receiver, params := [("alpha", .list [.num 0, .num 100])] }

/-- An activating single-input Hill promoter, `alpha = [0, 100]`. -/
def hll : Node := { id := "P", kind := .hill1, params := [("alpha", .list [.num 0, .num 100])] }

/-- The cascade: inducer `IPTG` drives `TF` through `Rc`, and `TF` drives the reporter `GFP` through
`P`. -/
def cascade : GRN where
  nodes := [ { id := "IPTG", kind := .supplement }, rcv, { id := "TF", kind := .regulator }, hll,
             { id := "GFP", kind := .reporter } ]
  edges := [ ⟨"IPTG", "Rc", 0⟩, ⟨"Rc", "TF", 0⟩, ⟨"TF", "P", 0⟩, ⟨"P", "GFP", 0⟩ ]

theorem cascade_ops : cascade.operators = [rcv, hll] := rfl

/-- The regulator species `TF`. -/
def sTF : cascade.Species := ⟨"TF", by decide⟩

/-- The reporter species `GFP`. -/
def sGFP : cascade.Species := ⟨"GFP", by decide⟩

/-- The cascade is acyclic, from the decidable Bool cycle check. -/
theorem cascade_acyclic : cascade.Acyclic := acyclic_of_acyclicBool cascade (by decide)

/-- The receiver strictly activates its inducer input. -/
theorem rcv_strict : rcv.StrictActivatingAt 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show (0:ℝ) < 1; norm_num
  · show (0:ℝ) < 2; norm_num
  · show ((0:ℚ):ℝ) < ((100:ℚ):ℝ); norm_num

/-- The Hill promoter strictly activates its regulator input. -/
theorem hll_strict : hll.StrictActivatingAt 0 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show (0:ℝ) < 1; norm_num
  · show (0:ℝ) < 2; norm_num
  · show ((0:ℚ):ℝ) < ((100:ℚ):ℝ); norm_num

/-- The strict monotone path `IPTG → Rc → TF → P → GFP`: the inducer drives `TF` through the receiver,
and `TF` drives the reporter `GFP` through the Hill promoter. -/
theorem cascade_path : StrictPath cascade "IPTG" sGFP :=
  StrictPath.step sGFP
    (StrictPath.base sTF (op := rcv) (by rw [cascade_ops]; exact List.mem_cons_self)
      (by decide) rcv_strict (by decide))
    (op := hll) (by rw [cascade_ops]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    (by decide) hll_strict (by decide)

/-! ## Well-formedness of the cascade -/

/-- The operators of the cascade are exactly the receiver and the Hill promoter. -/
theorem cascade_op_cases {op : Node} (hop : op ∈ cascade.operators) : op = rcv ∨ op = hll := by
  rw [cascade_ops] at hop; simpa using hop

theorem op_rnested {op : Node} (h : op = rcv ∨ op = hll) :
    op.rnested "alpha" = ([[], []] : List (List ℝ)) := by rcases h with rfl | rfl <;> rfl

theorem op_rlistK {op : Node} (h : op = rcv ∨ op = hll) : op.rlist "K" = ([] : List ℝ) := by
  rcases h with rfl | rfl <;> rfl

/-- `getD` into the `[[], []]` nested list is empty at every index. -/
theorem getD_emptyPair (i : ℕ) : ([[], []] : List (List ℝ)).getD i [] = [] := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) =>
      exact List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)

/-- The cascade is well-posed with unit degradation and a zero base inducer. -/
def cascadeWP : cascade.WellPosed where
  inducer := fun _ => 0
  inducer_nonneg := fun _ => le_refl 0
  γ := fun _ => 1
  γ_pos := fun _ => one_pos
  rate_nonneg := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) ≤ 0; norm_num)
  K_pos := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) < 1; norm_num)
  a0_nonneg := by
    intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) ≤ ((0:ℚ):ℝ); norm_num)
  a1_nonneg := by
    intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) ≤ ((100:ℚ):ℝ); norm_num)
  a2_nonneg := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) ≤ 0; norm_num)
  a3_nonneg := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) ≤ 0; norm_num)
  K1_pos := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) < 1; norm_num)
  K2_pos := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> (show (0:ℝ) < 1; norm_num)
  sum_wp := by
    intro op hop i
    have hc := cascade_op_cases hop
    have hrn : ((op.rnested "alpha").getD i []).getD 0 0 = (0:ℝ) ∧
        ((op.rnested "alpha").getD i []).getD 1 0 = (0:ℝ) := by
      rw [op_rnested hc, getD_emptyPair i]; exact ⟨rfl, rfl⟩
    have hrk : (op.rlist "K").getD i 1 = (1:ℝ) := by rw [op_rlistK hc]; simp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hrn.1, hrn.2, hrk] <;> norm_num
  alpha_wf := by intro op hop; rcases cascade_op_cases hop with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- Every cascade operator is `Regular` (positive `K`, nonnegative `n`). -/
theorem cascade_regular : ∀ op ∈ cascade.operators, op.Regular := by
  intro op hop
  rcases cascade_op_cases hop with rfl | rfl <;>
    exact ⟨by show (0:ℝ) < 1; norm_num, by show (0:ℝ) ≤ 2; norm_num⟩

/-- Every cascade operator is `MonoActivating`. -/
theorem cascade_monoActivating : ∀ op ∈ cascade.operators, op.MonoActivating := by
  intro op hop
  rcases cascade_op_cases hop with rfl | rfl <;>
    exact ⟨by show (0:ℝ) < 1; norm_num, by show (0:ℝ) ≤ 2; norm_num,
      by show ((0:ℚ):ℝ) ≤ ((100:ℚ):ℝ); norm_num⟩

/-! ## The payoff: a unique EC50 read from the wiring -/

/-- **The cascade's reporter has a unique EC50.** For any target reporter level `L` between the responses
at `lo` and `hi`, exactly one inducer level in `[lo, hi]` realizes it. Every hypothesis of
`grn_reporter_ec50_of_strictPath` is discharged concretely: acyclicity by the Bool cycle check, the
well-formedness structures above, and the strict-monotonicity side condition by `cascade_path`. -/
theorem cascade_ec50 {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi) {L : ℝ}
    (hL : L ∈ Set.Icc
      (steadyFam (cascade.regulates_wf cascade_acyclic) cascadeWP.γ
        (fun u i x => cascade.prodOf (inducerAt cascadeWP.inducer "IPTG" u) i x) lo sGFP)
      (steadyFam (cascade.regulates_wf cascade_acyclic) cascadeWP.γ
        (fun u i x => cascade.prodOf (inducerAt cascadeWP.inducer "IPTG" u) i x) hi sGFP)) :
    ∃! u, u ∈ Set.Icc lo hi ∧
      steadyFam (cascade.regulates_wf cascade_acyclic) cascadeWP.γ
        (fun u i x => cascade.prodOf (inducerAt cascadeWP.inducer "IPTG" u) i x) u sGFP = L :=
  cascade.grn_reporter_ec50_of_strictPath cascade_acyclic cascadeWP "IPTG" (by decide) sGFP
    cascade_regular cascade_monoActivating cascade_path hlo hle hL

end GRN.ReachExample
