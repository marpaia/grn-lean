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

/-! ## The cascade is the functor's real steady state

A linear cascade instantiates the feedforward IR directly: species `Fin n`, species `k` produced by
stage `k` driven by species `k-1` (or the inducer at the head). `linearChain_steady` shows the functor's
own `steadyPoint` at each species equals the cascade dose-response of the stages up to it, so
`linearChain_reporter` identifies the reporter's steady level with `cascadeResponse` — the EC50 of which is
already `cascade_ec50`. This closes "EC50 through the WF-recursion `steadyPoint`" for the cascade class. -/

/-- Appending a stage post-composes its map onto the cascade response. -/
theorem cascadeResponse_snoc (l : List StageParams) (s : StageParams) (u : ℝ) :
    cascadeResponse (l ++ [s]) u = stageMap s (cascadeResponse l u) := by
  induction l generalizing u with
  | nil => rfl
  | cons a rest ih => simp only [List.cons_append, cascadeResponse, ih]

/-- A linear cascade as a feedforward system over `Fin stages.length`: species `k` is stage `k`, driven by
species `k-1`, or by the inducer `u` at the head (`k = 0`). -/
noncomputable def linearChain (stages : List StageParams) (u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ s ∈ stages, s.Activating) :
    FeedforwardSystem (Fin stages.length) (fun j i => j.val + 1 = i.val) where
  wf := Subrelation.wf
    (show Subrelation (fun j i : Fin stages.length => j.val + 1 = i.val) (fun j i => j.val < i.val)
      from fun {_ _} h => by omega)
    (InvImage.wf Fin.val Nat.lt_wfRel.wf)
  γ := fun i => (stages.get i).γ
  hγ := fun i => (hs _ (stages.get_mem i)).2.2.2.1
  prod := fun i x => hill (stages.get i).a0 (stages.get i).a1 (stages.get i).K (stages.get i).n
    (if _h : 0 < i.val then x ⟨i.val - 1, by have := i.isLt; omega⟩ else u)
  local' := fun i x y hxy => by
    by_cases h : 0 < i.val
    · simp only [dif_pos h]
      have hr : (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin stages.length).val + 1 = i.val :=
        Nat.sub_add_cancel h
      rw [hxy ⟨i.val - 1, by have := i.isLt; omega⟩ hr]
    · simp only [dif_neg h]
  nonneg := fun i x hx => by
    have ha := hs _ (stages.get_mem i)
    refine hill_nonneg ha.1 ha.2.2.2.2 (le_of_lt (lt_of_le_of_lt ha.2.2.2.2 ha.2.2.1)) _ ?_
    by_cases h : 0 < i.val
    · simp only [dif_pos h]; exact hx _
    · simp only [dif_neg h]; exact hu

theorem linearChain_gamma (stages : List StageParams) (u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ s ∈ stages, s.Activating) (i : Fin stages.length) :
    (linearChain stages u hu hs).γ i = (stages.get i).γ := rfl

theorem linearChain_prod (stages : List StageParams) (u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ s ∈ stages, s.Activating) (i : Fin stages.length) (x : Fin stages.length → ℝ) :
    (linearChain stages u hu hs).prod i x =
      hill (stages.get i).a0 (stages.get i).a1 (stages.get i).K (stages.get i).n
        (if _h : 0 < i.val then x ⟨i.val - 1, by have := i.isLt; omega⟩ else u) := rfl

/-- **The cascade is the functor's steady state.** For a linear chain, the WF-recursion `steadyPoint` at
species `i` equals the cascade dose-response of the stages up to and including `i`. -/
theorem linearChain_steady (stages : List StageParams) (u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ s ∈ stages, s.Activating) (i : Fin stages.length) :
    (linearChain stages u hu hs).steadyPoint i = cascadeResponse (stages.take (i.val + 1)) u := by
  refine (linearChain stages u hu hs).wf.induction
    (C := fun i => (linearChain stages u hu hs).steadyPoint i =
      cascadeResponse (stages.take (i.val + 1)) u) i (fun i ih => ?_)
  have hik : i.val < stages.length := i.isLt
  have htake : stages.take (i.val + 1) = stages.take i.val ++ [stages.get i] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hik]; rfl
  rw [htake, cascadeResponse_snoc, FeedforwardSystem.steadyPoint_eq, linearChain_prod,
    linearChain_gamma, stageMap]
  congr 1
  by_cases h : 0 < i.val
  · have hr : (⟨i.val - 1, by have := i.isLt; omega⟩ : Fin stages.length).val + 1 = i.val :=
      Nat.sub_add_cancel h
    rw [dif_pos h, dif_pos hr, ih ⟨i.val - 1, by have := i.isLt; omega⟩ hr, hr]
  · rw [dif_neg h]
    have h0 : i.val = 0 := by omega
    rw [h0]
    rfl

/-- **The reporter's steady level is the cascade dose-response.** For a nonempty chain, the functor's
`steadyPoint` at the last species is `cascadeResponse stages u`, whose EC50 is `cascade_ec50`. -/
theorem linearChain_reporter (stages : List StageParams) (u : ℝ) (hu : 0 ≤ u)
    (hs : ∀ s ∈ stages, s.Activating) (hne : stages ≠ []) :
    (linearChain stages u hu hs).steadyPoint ⟨stages.length - 1, by
      have := List.length_pos_of_ne_nil hne; omega⟩ = cascadeResponse stages u := by
  rw [linearChain_steady]
  congr 1
  have := List.length_pos_of_ne_nil hne
  rw [Nat.sub_add_cancel this, List.take_length]

/-! ## General-DAG EC50 through the steady state

The capstone of Frontier A: any acyclic feedforward system whose reporter dose-response is continuous on
`[0,∞)` (`steadyFam_continuousOn`) and strictly monotone in the inducer (chained from `steadyFam_lt_base`
and `steadyFam_lt_step`) has a **unique EC50** — every intermediate reporter level is reached at exactly one
inducer value. This lifts `ec50_exists_unique` onto the functor's real WF-recursion `steadyPoint` for
arbitrary acyclic topologies, not just linear cascades. -/

/-- **A feedforward reporter has a unique EC50.** If the reporter's steady level is continuous and strictly
monotone in the inducer on `[lo, hi]`, every level between the endpoints is hit at exactly one inducer
value. Continuity comes from `steadyFam_continuousOn`; strict monotonicity from chaining `steadyFam_lt_base`
/ `steadyFam_lt_step` along a regulation path to the reporter. -/
theorem steadyFam_ec50 {ι : Type*} {r : ι → ι → Prop} (wf : WellFounded r) (γ : ι → ℝ)
    (prod : ℝ → ι → (ι → ℝ) → ℝ) (top : ι) {lo hi : ℝ} (hle : lo ≤ hi)
    (hcont : ContinuousOn (fun u => steadyFam wf γ prod u top) (Set.Icc lo hi))
    (hstrict : StrictMonoOn (fun u => steadyFam wf γ prod u top) (Set.Icc lo hi))
    {L : ℝ} (hL : L ∈ Set.Icc (steadyFam wf γ prod lo top) (steadyFam wf γ prod hi top)) :
    ∃! u, u ∈ Set.Icc lo hi ∧ steadyFam wf γ prod u top = L :=
  ec50_exists_unique hle hcont hstrict hL

/-- A parameterized direct sensor: the reporter reads the inducer `u` through one Hill response,
independent of the (single, unregulated) state coordinate. -/
noncomputable def paramDirect (a0 a1 K n : ℝ) : ℝ → Fin 1 → (Fin 1 → ℝ) → ℝ :=
  fun u _ _ => hill a0 a1 K n u

/-- **The A pipeline, end to end on Hill kinetics.** The parameterized direct sensor's steady reporter
level has a unique EC50 — continuity from `steadyFam_continuousOn`, strict monotonicity from
`steadyFam_lt_base` (with `steadyFam_mono` for the ambient order), assembled by `steadyFam_ec50`. This
exercises the whole of Frontier A against the real Hill response, not an abstract hypothesis. -/
theorem paramDirect_ec50 {a0 a1 K n γ lo hi : ℝ}
    (hK : 0 < K) (hn : 0 < n) (ha : a0 < a1) (hγ : 0 < γ) (ha0 : 0 ≤ a0)
    (hlo : 0 ≤ lo) (hle : lo ≤ hi) {L : ℝ}
    (hL : L ∈ Set.Icc (steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) lo 0)
      (steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) hi 0)) :
    ∃! u, u ∈ Set.Icc lo hi ∧
      steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) u 0 = L := by
  have ha1 : 0 ≤ a1 := le_of_lt (lt_of_le_of_lt ha0 ha)
  have hγi : ∀ _ : Fin 1, 0 < γ := fun _ => hγ
  have hprod : ∀ i : Fin 1, ContinuousOn (fun v : ℝ × (Fin 1 → ℝ) => paramDirect a0 a1 K n v.1 i v.2)
      (Set.Ici 0 ×ˢ Set.univ.pi (fun _ => Set.Ici 0)) := by
    intro i
    simp only [paramDirect]
    exact (hill_continuousOn hK hn.le).comp continuous_fst.continuousOn
      (fun v hv => (Set.mem_prod.1 hv).1)
  have hnn : ∀ t ∈ Set.Ici (0 : ℝ), ∀ (k : Fin 1) x, (∀ l, 0 ≤ x l) → 0 ≤ paramDirect a0 a1 K n t k x :=
    fun t ht _ _ _ => hill_nonneg hK ha0 ha1 t ht
  have hcont : ContinuousOn
      (fun u => steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) u 0)
      (Set.Icc lo hi) :=
    (steadyFam_continuousOn wellFounded_lt _ hγi hnn hprod 0).mono (fun u hu => le_trans hlo hu.1)
  have hstrict : StrictMonoOn
      (fun u => steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) u 0)
      (Set.Icc lo hi) := by
    intro p hp q hq hpq
    have hp0 : 0 ≤ p := le_trans hlo hp.1
    have hq0 : 0 ≤ q := le_trans hlo hq.1
    have hnnp : ∀ (k : Fin 1) x, (∀ l, 0 ≤ x l) → 0 ≤ paramDirect a0 a1 K n p k x :=
      fun _ _ _ => hill_nonneg hK ha0 ha1 p hp0
    have hnnq : ∀ (k : Fin 1) x, (∀ l, 0 ≤ x l) → 0 ≤ paramDirect a0 a1 K n q k x :=
      fun _ _ _ => hill_nonneg hK ha0 ha1 q hq0
    have hle' : ∀ k, steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) p k
        ≤ steadyFam wellFounded_lt (fun _ : Fin 1 => γ) (paramDirect a0 a1 K n) q k :=
      steadyFam_mono wellFounded_lt hγi hnnp hnnq
        (fun _ _ _ => hill_monotoneOn hK hn.le ha.le (Set.mem_Ici.2 hp0) (Set.mem_Ici.2 hq0) hpq.le)
        (fun _ _ _ _ _ _ => le_refl _)
    exact steadyFam_lt_base wellFounded_lt hγi hnnp hnnq hle' (fun _ _ _ _ _ => le_refl _)
      (fun _ _ => hill_strictMonoOn hK hn ha (Set.mem_Ici.2 hp0) (Set.mem_Ici.2 hq0) hpq)
  exact steadyFam_ec50 wellFounded_lt _ (paramDirect a0 a1 K n) 0 hle hcont hstrict hL

end GRN.Dynamics
