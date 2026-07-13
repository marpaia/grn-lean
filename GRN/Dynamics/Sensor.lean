import Mathlib
import GRN.Dynamics.VectorField

/-!
# Tier 2 — the sensor theorem

The sensor certificate (`GRN.certifies · .sensor`, interaction-graph monotonicity) promises a well-posed
dose-response: a monotone input/output map with a unique half-maximal crossing (EC50). This file proves
that guarantee for the Hill-kinetic response, bottom-up:

* `hill_monotoneOn` / `hill_antitoneOn` — a single operator's response is monotone in its input,
  increasing when it activates (`a0 ≤ a1`) and decreasing when it represses. This is the atom the edge
  sign records.
* `hill_strictMonoOn` — the strict version, for a genuine (non-flat) activator.
* `cascade_monotoneOn` — a feedforward cascade, the composition of stage responses, is monotone.
* `ec50_unique` / `hill_ec50_unique` — a strictly monotone response meets any level at exactly one input,
  so the EC50 the certificate promises is well defined.

This is the analytic content of the Angeli–Sontag guarantee for the feedforward (acyclic) sensor topology.
The general assembled-ODE statement is the remaining frontier (see `GRN.Dynamics.VectorField`).
-/

open Real Set

namespace GRN.Dynamics

variable {a0 a1 K n : ℝ}

/-- An activating Hill operator (`a0 ≤ a1`) has a monotone (nondecreasing) response on `[0, ∞)`. -/
theorem hill_monotoneOn (hK : 0 < K) (hn : 0 ≤ n) (ha : a0 ≤ a1) :
    MonotoneOn (hill a0 a1 K n) (Ici 0) := by
  intro u hu v hv huv
  rw [mem_Ici] at hu hv
  have huK : (0:ℝ) ≤ u / K := div_nonneg hu hK.le
  have hvK : (0:ℝ) ≤ v / K := div_nonneg hv hK.le
  have hUK : u / K ≤ v / K := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right huv (inv_pos.2 hK).le
  have hr : (u / K) ^ n ≤ (v / K) ^ n := Real.rpow_le_rpow huK hUK hn
  have hru : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg huK n
  have hrv : (0:ℝ) ≤ (v / K) ^ n := Real.rpow_nonneg hvK n
  have h1 : (0:ℝ) < 1 + (u / K) ^ n := by linarith
  have h2 : (0:ℝ) < 1 + (v / K) ^ n := by linarith
  simp only [hill]
  rw [← sub_nonneg, div_sub_div _ _ (ne_of_gt h2) (ne_of_gt h1)]
  apply div_nonneg
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hr)]
  · exact (mul_pos h2 h1).le

/-- A repressing Hill operator (`a1 ≤ a0`) has an antitone (nonincreasing) response on `[0, ∞)`. -/
theorem hill_antitoneOn (hK : 0 < K) (hn : 0 ≤ n) (ha : a1 ≤ a0) :
    AntitoneOn (hill a0 a1 K n) (Ici 0) := by
  intro u hu v hv huv
  rw [mem_Ici] at hu hv
  have huK : (0:ℝ) ≤ u / K := div_nonneg hu hK.le
  have hvK : (0:ℝ) ≤ v / K := div_nonneg hv hK.le
  have hUK : u / K ≤ v / K := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right huv (inv_pos.2 hK).le
  have hr : (u / K) ^ n ≤ (v / K) ^ n := Real.rpow_le_rpow huK hUK hn
  have hru : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg huK n
  have hrv : (0:ℝ) ≤ (v / K) ^ n := Real.rpow_nonneg hvK n
  have h1 : (0:ℝ) < 1 + (u / K) ^ n := by linarith
  have h2 : (0:ℝ) < 1 + (v / K) ^ n := by linarith
  simp only [hill]
  rw [← sub_nonneg, div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
  apply div_nonneg
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hr)]
  · exact (mul_pos h1 h2).le

/-- A Hill operator with nonnegative levels keeps a nonnegative input nonnegative — so cascaded stages
stay in the `[0, ∞)` domain. -/
theorem hill_nonneg (hK : 0 < K) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ hill a0 a1 K n u := by
  have hr : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg (div_nonneg hu hK.le) n
  simp only [hill]
  apply div_nonneg
  · nlinarith [mul_nonneg ha1 hr]
  · linarith

/-- A strictly activating Hill operator (`a0 < a1`, positive coefficient) is strictly monotone on
`[0, ∞)` — so its dose-response is injective and its EC50 unique. -/
theorem hill_strictMonoOn (hK : 0 < K) (hn : 0 < n) (ha : a0 < a1) :
    StrictMonoOn (hill a0 a1 K n) (Ici 0) := by
  intro u hu v hv huv
  rw [mem_Ici] at hu hv
  have huK : (0:ℝ) ≤ u / K := div_nonneg hu hK.le
  have hvK : (0:ℝ) ≤ v / K := div_nonneg hv hK.le
  have hUK : u / K < v / K := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right huv (inv_pos.2 hK)
  have hr : (u / K) ^ n < (v / K) ^ n := Real.rpow_lt_rpow huK hUK hn
  have hru : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg huK n
  have hrv : (0:ℝ) ≤ (v / K) ^ n := Real.rpow_nonneg hvK n
  have h1 : (0:ℝ) < 1 + (u / K) ^ n := by linarith
  have h2 : (0:ℝ) < 1 + (v / K) ^ n := by linarith
  simp only [hill]
  rw [← sub_pos, div_sub_div _ _ (ne_of_gt h2) (ne_of_gt h1)]
  apply div_pos
  · nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 hr)]
  · exact mul_pos h2 h1

/-- A strictly repressing Hill operator (`a1 < a0`) is strictly antitone on `[0, ∞)`. -/
theorem hill_strictAntiOn (hK : 0 < K) (hn : 0 < n) (ha : a1 < a0) :
    StrictAntiOn (hill a0 a1 K n) (Ici 0) := by
  intro u hu v hv huv
  rw [mem_Ici] at hu hv
  have huK : (0:ℝ) ≤ u / K := div_nonneg hu hK.le
  have hvK : (0:ℝ) ≤ v / K := div_nonneg hv hK.le
  have hUK : u / K < v / K := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right huv (inv_pos.2 hK)
  have hr : (u / K) ^ n < (v / K) ^ n := Real.rpow_lt_rpow huK hUK hn
  have hru : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg huK n
  have hrv : (0:ℝ) ≤ (v / K) ^ n := Real.rpow_nonneg hvK n
  have h1 : (0:ℝ) < 1 + (u / K) ^ n := by linarith
  have h2 : (0:ℝ) < 1 + (v / K) ^ n := by linarith
  simp only [hill]
  rw [← sub_pos, div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
  apply div_pos
  · nlinarith [mul_pos (sub_pos.2 ha) (sub_pos.2 hr)]
  · exact mul_pos h1 h2

/-- A Hill operator's response is continuous on `[0, ∞)` — the input to the intermediate-value step that
locates the EC50 (T3). -/
theorem hill_continuousOn (hK : 0 < K) (hn : 0 ≤ n) :
    ContinuousOn (hill a0 a1 K n) (Ici 0) := by
  have hr : ContinuousOn (fun u : ℝ => (u / K) ^ n) (Ici 0) :=
    ((continuous_id.div_const K).continuousOn).rpow_const (fun _ _ => Or.inr hn)
  have hnum : ContinuousOn (fun u : ℝ => a0 + a1 * (u / K) ^ n) (Ici 0) :=
    continuousOn_const.add (continuousOn_const.mul hr)
  have hden : ContinuousOn (fun u : ℝ => 1 + (u / K) ^ n) (Ici 0) :=
    continuousOn_const.add hr
  have hne : ∀ u ∈ Ici (0:ℝ), (1 : ℝ) + (u / K) ^ n ≠ 0 := by
    intro u hu
    have : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg (div_nonneg (mem_Ici.mp hu) hK.le) n
    positivity
  exact hnum.div hden hne

/-- One feedforward stage: a Hill operator's kinetic parameters. -/
structure Stage where
  a0 : ℝ
  a1 : ℝ
  K : ℝ
  n : ℝ

/-- A stage's steady-state response. -/
noncomputable def Stage.resp (s : Stage) : ℝ → ℝ := hill s.a0 s.a1 s.K s.n

/-- A well-posed activating stage: positive constants, nonnegative and increasing levels. -/
def Stage.Activator (s : Stage) : Prop :=
  0 < s.K ∧ 0 ≤ s.n ∧ 0 ≤ s.a0 ∧ 0 ≤ s.a1 ∧ s.a0 ≤ s.a1

/-- A feedforward cascade's steady-state response: stages applied in series. -/
noncomputable def cascade : List Stage → ℝ → ℝ
  | [], u => u
  | s :: rest, u => cascade rest (s.resp u)

/-- A feedforward cascade of activating stages has a monotone dose-response on `[0, ∞)`: the composition
of monotone stage responses that each preserve the nonnegative domain. -/
theorem cascade_monotoneOn : ∀ (stages : List Stage), (∀ s ∈ stages, s.Activator) →
    MonotoneOn (cascade stages) (Ici 0)
  | [], _ => by intro u _ v _ huv; exact huv
  | s :: rest, h => by
    obtain ⟨hK, hn, ha0, ha1, ha⟩ := h s (by simp)
    have hrest : ∀ t ∈ rest, t.Activator := fun t ht => h t (by simp [ht])
    have hmono_s : MonotoneOn s.resp (Ici 0) := hill_monotoneOn hK hn ha
    have hmaps : MapsTo s.resp (Ici 0) (Ici 0) := by
      intro u hu; rw [mem_Ici] at hu ⊢; exact hill_nonneg hK ha0 ha1 u hu
    have hcomp := (cascade_monotoneOn rest hrest).comp hmono_s hmaps
    intro u hu v hv huv
    exact hcomp hu hv huv

/-- A strictly monotone response meets any level at most once: the half-maximal input (EC50) is unique. -/
theorem ec50_unique {f : ℝ → ℝ} (hf : StrictMonoOn f (Ici 0)) {L a b : ℝ}
    (ha : (0:ℝ) ≤ a) (hb : (0:ℝ) ≤ b) (hfa : f a = L) (hfb : f b = L) : a = b :=
  hf.injOn ha hb (hfa.trans hfb.symm)

/-- A strictly activating Hill sensor has a unique EC50: at most one input reaches any given output. -/
theorem hill_ec50_unique (hK : 0 < K) (hn : 0 < n) (ha : a0 < a1) {L a b : ℝ}
    (ha' : (0:ℝ) ≤ a) (hb' : (0:ℝ) ≤ b)
    (hfa : hill a0 a1 K n a = L) (hfb : hill a0 a1 K n b = L) : a = b :=
  ec50_unique (hill_strictMonoOn hK hn ha) ha' hb' hfa hfb

/-- **EC50 exists and is unique** (T3): a continuous strictly-monotone dose-response on `[lo, hi]` meets
every level between its endpoints at exactly one input. Existence by the intermediate value theorem,
uniqueness by strict monotonicity. -/
theorem ec50_exists_unique {f : ℝ → ℝ} {lo hi : ℝ} (hlo : lo ≤ hi)
    (hcont : ContinuousOn f (Icc lo hi)) (hmono : StrictMonoOn f (Icc lo hi))
    {L : ℝ} (hL : L ∈ Icc (f lo) (f hi)) :
    ∃! u, u ∈ Icc lo hi ∧ f u = L := by
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hlo hcont hL
  refine ⟨u, ⟨hu, hfu⟩, ?_⟩
  rintro v ⟨hv, hfv⟩
  exact hmono.injOn hv hu (hfv.trans hfu.symm)

end GRN.Dynamics
