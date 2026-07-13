import Mathlib
import GRN.Dynamics.Sensor
import GRN.Dynamics.Feedforward

/-!
# Tier 2 — EC50 through the functor (direct sensor)

The dose-response of a direct sensor — a reporter driven straight from the inducer — is its steady
reporter level as a function of the inducer, `hill(inducer)/γ`. This file shows that map *is* the
constructive steady state (`directSensor_steady`) and that it has a **unique EC50**
(`doseResponse_ec50`): a continuous, strictly monotone dose-response meets every intermediate level at
exactly one inducer value. This instantiates the abstract `ec50_exists_unique` on the functor's steady
state, closing the well-defined-EC50 half of the sensor guarantee for the direct case.
-/

namespace GRN.Dynamics

open Set

/-- The direct-sensor dose-response: the reporter's steady level as a function of the inducer. -/
noncomputable def doseResponse (a0 a1 K n γ u : ℝ) : ℝ := hill a0 a1 K n u / γ

/-- The direct sensor as a one-species feedforward system: the reporter produced by a single Hill
response of the (fixed) inducer level `u`. -/
noncomputable def directSensor (a0 a1 K n γ u : ℝ) (hγ : 0 < γ) (hu : 0 ≤ u)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hK : 0 < K) : FeedforwardSystem (Fin 1) (· < ·) where
  wf := wellFounded_lt
  γ := fun _ => γ
  hγ := fun _ => hγ
  prod := fun _ _ => hill a0 a1 K n u
  local' := fun _ _ _ _ => rfl
  nonneg := fun _ _ _ => hill_nonneg hK ha0 ha1 u hu

/-- The functor's steady state for the direct sensor is the dose-response. -/
theorem directSensor_steady (a0 a1 K n γ u : ℝ) (hγ : 0 < γ) (hu : 0 ≤ u)
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hK : 0 < K) :
    (directSensor a0 a1 K n γ u hγ hu ha0 ha1 hK).steadyPoint 0 = doseResponse a0 a1 K n γ u := by
  rw [FeedforwardSystem.steadyPoint_eq]
  rfl

/-- **A direct sensor's dose-response has a unique EC50.** For a strictly activating Hill sensor with
positive degradation, the steady reporter level is continuous and strictly increasing in the inducer, so
every level between the endpoints is reached at exactly one inducer value. -/
theorem doseResponse_ec50 {a0 a1 K n γ lo hi : ℝ}
    (hK : 0 < K) (hn : 0 < n) (ha : a0 < a1) (hγ : 0 < γ) (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    {L : ℝ} (hL : L ∈ Icc (doseResponse a0 a1 K n γ lo) (doseResponse a0 a1 K n γ hi)) :
    ∃! u, u ∈ Icc lo hi ∧ doseResponse a0 a1 K n γ u = L := by
  have hsub : Icc lo hi ⊆ Ici 0 := fun u hu => le_trans hlo hu.1
  refine ec50_exists_unique hle ?_ ?_ hL
  · exact ((hill_continuousOn hK hn.le).mono hsub).div_const γ
  · intro u hu v hv huv
    have h : hill a0 a1 K n u < hill a0 a1 K n v :=
      hill_strictMonoOn hK hn ha (hsub hu) (hsub hv) huv
    unfold doseResponse
    gcongr

end GRN.Dynamics
