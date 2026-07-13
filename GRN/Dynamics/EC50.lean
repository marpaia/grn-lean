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

/-! ## Multi-stage cascade dose-response -/

/-- One stage of a feedforward cascade: an activating Hill response with its degradation. -/
structure StageParams where
  a0 : ℝ
  a1 : ℝ
  K : ℝ
  n : ℝ
  γ : ℝ

/-- A well-posed strictly-activating stage. -/
def StageParams.Activating (s : StageParams) : Prop :=
  0 < s.K ∧ 0 < s.n ∧ s.a0 < s.a1 ∧ 0 < s.γ ∧ 0 ≤ s.a0

/-- A stage's steady input/output map: `hill(v)/γ`. -/
noncomputable def stageMap (s : StageParams) (v : ℝ) : ℝ := hill s.a0 s.a1 s.K s.n v / s.γ

theorem stageMap_nonneg (s : StageParams) (hs : s.Activating) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ stageMap s v := by
  obtain ⟨hK, _, ha, hγ, ha0⟩ := hs
  exact div_nonneg (hill_nonneg hK ha0 (le_of_lt (lt_of_le_of_lt ha0 ha)) v hv) hγ.le

theorem stageMap_mapsTo (s : StageParams) (hs : s.Activating) :
    MapsTo (stageMap s) (Ici 0) (Ici 0) :=
  fun _ hv => mem_Ici.mpr (stageMap_nonneg s hs (mem_Ici.mp hv))

theorem stageMap_continuousOn (s : StageParams) (hs : s.Activating) :
    ContinuousOn (stageMap s) (Ici 0) := by
  obtain ⟨hK, hn, _, _, _⟩ := hs
  exact (hill_continuousOn hK hn.le).div_const s.γ

theorem stageMap_strictMonoOn (s : StageParams) (hs : s.Activating) :
    StrictMonoOn (stageMap s) (Ici 0) := by
  obtain ⟨hK, hn, ha, hγ, _⟩ := hs
  intro u hu v hv huv
  have := hill_strictMonoOn hK hn ha hu hv huv
  unfold stageMap
  gcongr

/-- The multi-stage cascade dose-response: stages applied in series to the inducer. -/
noncomputable def cascadeResponse : List StageParams → ℝ → ℝ
  | [], u => u
  | s :: rest, u => cascadeResponse rest (stageMap s u)

theorem cascadeResponse_continuousOn : ∀ (stages : List StageParams),
    (∀ s ∈ stages, s.Activating) → ContinuousOn (cascadeResponse stages) (Ici 0)
  | [], _ => continuousOn_id
  | s :: rest, h => by
    have hs := h s (by simp)
    have hrest : ∀ t ∈ rest, t.Activating := fun t ht => h t (by simp [ht])
    exact (cascadeResponse_continuousOn rest hrest).comp (stageMap_continuousOn s hs)
      (stageMap_mapsTo s hs)

theorem cascadeResponse_strictMonoOn : ∀ (stages : List StageParams),
    (∀ s ∈ stages, s.Activating) → StrictMonoOn (cascadeResponse stages) (Ici 0)
  | [], _ => strictMonoOn_id
  | s :: rest, h => by
    have hs := h s (by simp)
    have hrest : ∀ t ∈ rest, t.Activating := fun t ht => h t (by simp [ht])
    exact (cascadeResponse_strictMonoOn rest hrest).comp (stageMap_strictMonoOn s hs)
      (stageMap_mapsTo s hs)

/-- **A multi-stage activating cascade has a unique EC50.** The dose-response is a composition of
strictly-monotone continuous stage maps, so it meets every intermediate level at exactly one inducer
value. -/
theorem cascade_ec50 (stages : List StageParams) (h : ∀ s ∈ stages, s.Activating)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hle : lo ≤ hi) {L : ℝ}
    (hL : L ∈ Icc (cascadeResponse stages lo) (cascadeResponse stages hi)) :
    ∃! u, u ∈ Icc lo hi ∧ cascadeResponse stages u = L := by
  have hsub : Icc lo hi ⊆ Ici 0 := fun u hu => le_trans hlo hu.1
  exact ec50_exists_unique hle
    ((cascadeResponse_continuousOn stages h).mono hsub)
    ((cascadeResponse_strictMonoOn stages h).mono hsub) hL

/-! ## Sign-consistent cascade: unique EC50 with repressors -/

/-- A well-posed *sign-consistent* stage: strictly activating or strictly repressing. -/
def StageParams.SignActivating (s : StageParams) : Prop :=
  0 < s.K ∧ 0 < s.n ∧ 0 < s.γ ∧ 0 ≤ s.a0 ∧ 0 ≤ s.a1 ∧ (s.a0 < s.a1 ∨ s.a1 < s.a0)

theorem stageMap_mapsTo_sign (s : StageParams) (hs : s.SignActivating) :
    MapsTo (stageMap s) (Ici 0) (Ici 0) := by
  obtain ⟨hK, _, hγ, ha0, ha1, _⟩ := hs
  exact fun v hv => mem_Ici.mpr (div_nonneg (hill_nonneg hK ha0 ha1 v (mem_Ici.mp hv)) hγ.le)

/-- Each sign-consistent stage map is injective on `[0, ∞)` — strictly monotone or strictly antitone. -/
theorem stageMap_injOn (s : StageParams) (hs : s.SignActivating) : InjOn (stageMap s) (Ici 0) := by
  obtain ⟨hK, hn, hγ, _, _, hdir⟩ := hs
  rcases hdir with h | h
  · refine StrictMonoOn.injOn (fun u hu v hv huv => ?_)
    have := hill_strictMonoOn hK hn h hu hv huv
    unfold stageMap; gcongr
  · refine StrictAntiOn.injOn (fun u hu v hv huv => ?_)
    have := hill_strictAntiOn hK hn h hu hv huv
    unfold stageMap; gcongr

theorem cascadeResponse_injOn : ∀ (stages : List StageParams),
    (∀ s ∈ stages, s.SignActivating) → InjOn (cascadeResponse stages) (Ici 0)
  | [], _ => Set.injOn_id _
  | s :: rest, h => by
    have hs := h s (by simp)
    have hrest : ∀ t ∈ rest, t.SignActivating := fun t ht => h t (by simp [ht])
    exact (cascadeResponse_injOn rest hrest).comp (stageMap_injOn s hs) (stageMap_mapsTo_sign s hs)

/-- **A sign-consistent cascade has a unique EC50** (at most one): with each stage strictly activating or
repressing, the dose-response is injective, so any level is reached at one inducer value at most —
repressors and mixed-sign cascades included. -/
theorem cascade_ec50_unique (stages : List StageParams) (h : ∀ s ∈ stages, s.SignActivating)
    {lo hi : ℝ} (hlo : 0 ≤ lo) {L u v : ℝ} (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi)
    (hfu : cascadeResponse stages u = L) (hfv : cascadeResponse stages v = L) : u = v := by
  have hsub : Icc lo hi ⊆ Ici 0 := fun w hw => le_trans hlo hw.1
  exact cascadeResponse_injOn stages h (hsub hu) (hsub hv) (hfu.trans hfv.symm)

end GRN.Dynamics
