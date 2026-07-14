import Mathlib
import GRN.Dynamics.GRNEc50
import GRN.Dynamics.Spin

/-!
# The reconvergent (sign-consistent) sensor

A sensor GRN need not be a pure activation cascade: it may mix activation and repression and reconverge,
yet still be a monotone system whenever its signed interaction graph is *balanced* (`isMonotoneEdges`).
The classical device (Angeli–Sontag) is a **spin flip**: with the balancing spin `σ : String → Int`
(`GRN.Dynamics.Spin`), pass to flipped coordinates `y_i = σ_i · x_i`. In these coordinates the interpreted
production is cooperative — monotone *increasing* in the flipped inputs — because each edge of sign `s`
contributes `σ_i · s · σ_j = 1` by `balance`.

The dose-response monotonicity then rides the existing feedforward engine (`steadyFam_mono`) in the flipped
frame and unflips to the original coordinates, where the reporter's response is monotone or antitone
according to its own spin `σ_reporter` — the directional response the sensor certificate promises for a
reconvergent circuit.
-/

namespace GRN

open Dynamics Set

/-- σ (a `String → ℝ` spin) takes values `±1` on every regulated species. -/
def IsSpin (σ : String → ℝ) (g : GRN) : Prop := ∀ i : g.Species, σ i.1 = 1 ∨ σ i.1 = -1

/-- σ balances the signed interaction graph: each edge `(j, i, s)` has `σ i = s · σ j`. -/
def Balances (σ : String → ℝ) (g : GRN) : Prop :=
  ∀ e ∈ signedInteractionGraph g, σ e.2.1 = (e.2.2 : ℝ) * σ e.1

/-- A single-input operator that monotonically *represses* its input (`a1 ≤ a0`, with `K > 0`, `n ≥ 0`) —
the repressing counterpart of `Node.MonoActivating`. -/
def _root_.Node.MonoRepressing (op : Node) : Prop :=
  match op.kind with
  | .receiver | .hill1 =>
      0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0
  | _ => False

/-- An operator with a definite monotone sign: activating or repressing. -/
def _root_.Node.MonoSigned (op : Node) : Prop := op.MonoActivating ∨ op.MonoRepressing

/-- The flipped production of species `i`: the interpreted production read in spin-adjusted coordinates
`x_j = σ_j · y_j`, then scaled by `σ_i`. On a balanced network this is monotone increasing in the flipped
inputs. -/
noncomputable def flipProd (g : GRN) (σ : String → ℝ) (inducer : String → ℝ)
    (i : g.Species) (y : g.Species → ℝ) : ℝ :=
  σ i.1 * g.prodOf inducer i (fun j => σ j.1 * y j)

/-- The flipped production with the chosen inducer's level as a parameter — the flipped-frame production
family fed to `steadyFam`. -/
noncomputable def flipProdParam (g : GRN) (σ : String → ℝ) (base : String → ℝ) (s : String) :
    ℝ → g.Species → (g.Species → ℝ) → ℝ :=
  fun u i y => σ i.1 * g.prodOf (inducerAt base s u) i (fun j => σ j.1 * y j)

/-- Raising the chosen inducer's level does not lower any flipped production: the inducer drives the
network positively in flipped coordinates. -/
def FlipDrive (g : GRN) (σ : String → ℝ) (base : String → ℝ) (s : String) : Prop :=
  ∀ (i : g.Species) (y : g.Species → ℝ) (p q : ℝ), p ≤ q →
    g.flipProdParam σ base s p i y ≤ g.flipProdParam σ base s q i y

/-- With coincident basal/saturation levels a single-input Hill response is the constant `a0` (on the
nonnegative input domain): the operator carries no edge and its rate is flat. -/
theorem hill_const {a0 a1 K n u : ℝ} (hK : 0 < K) (hu : 0 ≤ u) (ha : a0 = a1) :
    hill a0 a1 K n u = a0 := by
  subst ha
  have hr : (0:ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg (div_nonneg hu hK.le) n
  have hden : (0:ℝ) < 1 + (u / K) ^ n := by linarith
  simp only [Dynamics.hill]
  rw [div_eq_iff (ne_of_gt hden)]; ring

/-- The analytic heart of flip-cooperativity for one single-input Hill operator: in flipped coordinates
`σ_j · y`, an operator of definite sign whose spin satisfies balance (`σ_i = s·σ_j`) has `σ_i`-scaled rate
monotone increasing in the flipped input `y`. Activation with `σ_i = σ_j` and repression with
`σ_i = -σ_j` both collapse, by `σ_i · s · σ_j = 1`, to a genuine increase. -/
theorem flip_hill_step {a0 a1 K n σi σj y0 y0' : ℝ}
    (hK : 0 < K) (hn : 0 ≤ n) (hσj : σj = 1 ∨ σj = -1)
    (hp : 0 ≤ σj * y0) (hq : 0 ≤ σj * y0') (hyle : y0 ≤ y0')
    (h : (a0 ≤ a1 ∧ σi = σj) ∨ (a1 ≤ a0 ∧ σi = -σj)) :
    σi * hill a0 a1 K n (σj * y0) ≤ σi * hill a0 a1 K n (σj * y0') := by
  rcases hσj with hj | hj <;> subst hj
  · rcases h with ⟨hact, hrel⟩ | ⟨hrep, hrel⟩
    · have hh := hill_monotoneOn hK hn hact (Set.mem_Ici.mpr hp) (Set.mem_Ici.mpr hq)
        (by linarith [hyle])
      rw [hrel]; linarith [hh]
    · have hh := hill_antitoneOn hK hn hrep (Set.mem_Ici.mpr hp) (Set.mem_Ici.mpr hq)
        (by linarith [hyle])
      rw [show σi = -1 by linarith [hrel]]; linarith [hh]
  · rcases h with ⟨hact, hrel⟩ | ⟨hrep, hrel⟩
    · have hh := hill_monotoneOn hK hn hact (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr hp)
        (by linarith [hyle])
      rw [hrel]; linarith [hh]
    · have hh := hill_antitoneOn hK hn hrep (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr hp)
        (by linarith [hyle])
      rw [show σi = 1 by linarith [hrel]]; linarith [hh]

/-- A single-input Hill/receiver operator that produces species `i` from a strictly-signed first input
`j0` contributes the corresponding signed edge `(j0, i, s)` to the interaction graph — the bridge that lets
`balance` fix `σ_i = s·σ_j0`. -/
theorem hill_edge_mem (g : GRN) {op : Node} (hop : op ∈ g.operators)
    (hkrh : op.kind = .receiver ∨ op.kind = .hill1)
    {b0 b1 : ℚ} {restA : List ℚ} (hab : op.alphaNums = b0 :: b1 :: restA)
    {j0 : String} {restIn : List String} (hin : g.inputsOf op.id = j0 :: restIn)
    {i : String} (hiout : i ∈ g.outputsOf op.id)
    {s : Int} (hps : pairSign b0 b1 = some s) :
    ((j0, i, s) : SignedEdge) ∈ signedInteractionGraph g := by
  have hos : g.opEdgeSigns op = [pairSign b0 b1] := by
    rcases hkrh with h | h <;> simp only [opEdgeSigns, operatorInputSigns, h, hab]
  have hmem : ((j0, i, s) : SignedEdge) ∈
      edgesFrom (g.opEdgeSigns op) (g.inputsOf op.id) (g.outputsOf op.id) := by
    rw [hos, hin, hps]
    simp only [edgesFrom, List.append_nil]
    exact List.mem_map.mpr ⟨i, hiout, rfl⟩
  have gen : ∀ L, op ∈ L → ((j0, i, s) : SignedEdge) ∈ opEdges g L := by
    intro L
    induction L with
    | nil => intro hL; simp at hL
    | cons a t ih =>
      intro hL
      simp only [opEdges]
      rcases List.mem_cons.mp hL with heq | hmt
      · subst heq; exact List.mem_append_left _ hmem
      · exact List.mem_append_right _ (ih hmt)
  exact gen g.operators hop

/-- **Cooperativity in flipped coordinates.** For a well-posed GRN with a balancing spin `σ` whose every
single-input operator is monotone-signed, the flipped production is monotone increasing in the flipped
regulator coordinates — each edge of sign `s` contributes `σ_i · s · σ_j = 1` by `balance`.

The monotonicity is in the *flipped* inputs `y` (hypothesis `hle : y j ≤ y' j`), while `hnn`/`hnn'` keep
the *physical* concentrations `σ_j · y_j` nonnegative, the domain on which the Hill response is monotone.
`hkind` restricts to single-input operators (`source`/`receiver`/`hill1`) and `hlen` asks their
`alpha = [a0, a1]` to carry both levels, so that a non-flat rate always emits a graph edge for `balance` to
read; these are exactly the well-formedness facts under which the sign bookkeeping is sound. -/
theorem flipProd_mono (g : GRN) (σ : String → ℝ) (wp : g.WellPosed)
    (hspin : IsSpin σ g) (hbal : Balances σ g)
    (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (hkind : ∀ op ∈ g.operators, op.kind = .source ∨ op.kind = .receiver ∨ op.kind = .hill1)
    (hlen : ∀ op ∈ g.operators, 2 ≤ op.alphaNums.length)
    (i : g.Species) {y y' : g.Species → ℝ}
    (hnn : ∀ j, 0 ≤ σ j.1 * y j) (hnn' : ∀ j, 0 ≤ σ j.1 * y' j)
    (hle : ∀ j, g.regulates j i → y j ≤ y' j) :
    g.flipProd σ wp.inducer i y ≤ g.flipProd σ wp.inducer i y' := by
  -- Per-operator flip-cooperativity, scaled by `σ_i`.
  have key : ∀ op ∈ g.operators.filter (fun op => decide ((i : String) ∈ g.outputsOf op.id)),
      σ i.1 * g.opRate (g.valuation wp.inducer (fun j => σ j.1 * y j)) op
        ≤ σ i.1 * g.opRate (g.valuation wp.inducer (fun j => σ j.1 * y' j)) op := by
    intro op hopf
    have hop : op ∈ g.operators := List.mem_of_mem_filter hopf
    have hiout : (i : String) ∈ g.outputsOf op.id := by
      have h := List.of_mem_filter hopf; simpa using h
    have hMS := hsigned op hop
    rcases hkind op hop with hs | hkrh
    · -- source: rate is a constant, independent of the state
      simp [GRN.opRate, GRN.opRateV, hs]
    · -- receiver / hill1: the single-input Hill response
      have hval_eq : ∀ v : String → ℝ, g.opRate v op
          = hill ((op.alphaNums.map (fun q => (q : ℝ))).getD 0 0)
                 ((op.alphaNums.map (fun q => (q : ℝ))).getD 1 0)
                 (op.rparam "K" 1) (op.rparam "n" 2)
                 (((g.inputsOf op.id).map v).headD 0) := by
        intro v; rcases hkrh with h | h <;> simp only [GRN.opRate, GRN.opRateV, h]
      simp only [hval_eq]
      -- reduced monotone-signed data
      have hsig' : (0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2 ∧
            (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0) ∨
          (0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2 ∧
            (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0) := by
        rcases hMS with h | h
        · left; rcases hkrh with hk' | hk' <;> (simp only [Node.MonoActivating, hk'] at h; exact h)
        · right; rcases hkrh with hk' | hk' <;> (simp only [Node.MonoRepressing, hk'] at h; exact h)
      -- the alpha vector carries both levels (well-formedness)
      obtain ⟨b0, b1, restA, hab⟩ : ∃ b0 b1 restA, op.alphaNums = b0 :: b1 :: restA := by
        have hL := hlen op hop
        rcases hAN : op.alphaNums with _ | ⟨c0, _ | ⟨c1, r⟩⟩
        · simp [hAN] at hL
        · simp [hAN] at hL
        · exact ⟨c0, c1, r, rfl⟩
      have ha0 : (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 = (b0 : ℝ) := by rw [hab]; simp
      have ha1 : (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 = (b1 : ℝ) := by rw [hab]; simp
      -- reduce the first-input value
      rcases hinp : g.inputsOf op.id with _ | ⟨j0, restIn⟩
      · simp
      · by_cases hj0 : j0 ∈ g.regIds
        · simp only [List.map_cons, List.headD_cons, GRN.valuation, dif_pos hj0]
          set J0 : g.Species := ⟨j0, hj0⟩ with hJ0
          have hpnn : 0 ≤ σ J0.1 * y J0 := hnn J0
          have hqnn : 0 ≤ σ J0.1 * y' J0 := hnn' J0
          have hyle0 : y J0 ≤ y' J0 :=
            hle J0 ⟨op, hop, by rw [hinp]; exact List.mem_cons_self, hiout⟩
          rcases hsig' with ⟨hK, hn, hact⟩ | ⟨hK, hn, hrep⟩
          · rcases eq_or_lt_of_le hact with heq | hlt
            · rw [hill_const hK hpnn heq, hill_const hK hqnn heq]
            · have hb : b0 < b1 := by
                have := hlt; rw [ha0, ha1] at this; exact_mod_cast this
              have hps : pairSign b0 b1 = some 1 := by
                simp only [pairSign, gt_iff_lt]; rw [if_pos hb]
              have hedge := hill_edge_mem g hop hkrh hab hinp hiout hps
              have hrel : σ i.1 = σ J0.1 := by have := hbal _ hedge; simpa using this
              exact flip_hill_step hK hn (hspin J0) hpnn hqnn hyle0
                (Or.inl ⟨le_of_lt hlt, hrel⟩)
          · rcases eq_or_lt_of_le hrep with heq | hlt
            · rw [hill_const hK hpnn heq.symm, hill_const hK hqnn heq.symm]
            · have hb : b1 < b0 := by
                have := hlt; rw [ha0, ha1] at this; exact_mod_cast this
              have hps : pairSign b0 b1 = some (-1) := by
                simp only [pairSign, gt_iff_lt]
                rw [if_neg (not_lt.mpr hb.le), if_pos hb]
              have hedge := hill_edge_mem g hop hkrh hab hinp hiout hps
              have hrel : σ i.1 = -σ J0.1 := by have := hbal _ hedge; simpa using this
              exact flip_hill_step hK hn (hspin J0) hpnn hqnn hyle0
                (Or.inr ⟨le_of_lt hlt, hrel⟩)
        · simp [GRN.valuation, dif_neg hj0]
  -- Assemble: `σ_i` factors through the sum over producing operators.
  unfold flipProd
  rcases hspin i with hσi | hσi
  · rw [hσi]; simp only [one_mul]
    unfold GRN.prodOf
    refine List.sum_le_sum (fun op hopf => ?_)
    have hk := key op hopf; rw [hσi, one_mul, one_mul] at hk; exact hk
  · rw [hσi]
    unfold GRN.prodOf
    have hBA : ((g.operators.filter (fun op => decide ((i : String) ∈ g.outputsOf op.id))).map
          (g.opRate (g.valuation wp.inducer (fun j => σ j.1 * y' j)))).sum
        ≤ ((g.operators.filter (fun op => decide ((i : String) ∈ g.outputsOf op.id))).map
          (g.opRate (g.valuation wp.inducer (fun j => σ j.1 * y j)))).sum := by
      refine List.sum_le_sum (fun op hopf => ?_)
      have hk := key op hopf; rw [hσi] at hk; linarith [hk]
    linarith [hBA]

/-- **Physical nonnegativity in the flipped frame.** The flipped steady value `σ_i · x_i` is a nonnegative
physical concentration: `σ_i`-scaling the flipped steady point recovers `(σ_i)²·prodOf/γ_i`, and `prodOf`
is nonnegative on inputs that are themselves nonnegative physical concentrations — exactly the induction
hypothesis on `r`-earlier species. This is the domain predicate on which the flipped Hill response is
monotone, so it discharges the `hnn`/`hnn'` obligations of `flipProd_mono`. -/
theorem flip_steadyFam_nonneg (g : GRN) (hac : g.Acyclic) (σ : String → ℝ) (wp : g.WellPosed)
    (s : String) (u : ℝ) (hu : 0 ≤ u) (i : g.Species) :
    0 ≤ σ i.1 * steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u i := by
  classical
  refine (g.regulates_wf hac).induction
    (C := fun i => 0 ≤ σ i.1 *
      steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u i) i (fun i ih => ?_)
  have hx : ∀ j, 0 ≤ σ j.1 *
      (if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0) := by
    intro j; by_cases hj : g.regulates j i
    · rw [dif_pos hj]; exact ih j hj
    · rw [dif_neg hj, mul_zero]
  have hP : 0 ≤ g.prodOf (inducerAt wp.inducer s u) i
      (fun j => σ j.1 *
        (if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0)) :=
    g.prodOf_nonneg (wp.setInducer s u hu) i _ hx
  rw [steadyFam_eq (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u i]
  have hflip : g.flipProdParam σ wp.inducer s u i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0)
      = σ i.1 * g.prodOf (inducerAt wp.inducer s u) i
          (fun j => σ j.1 *
            (if _h : g.regulates j i then
              steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0)) := rfl
  rw [hflip]
  set P := g.prodOf (inducerAt wp.inducer s u) i
    (fun j => σ j.1 *
      (if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0))
  have harith : σ i.1 * (σ i.1 * P / wp.γ i) = σ i.1 * σ i.1 * P / wp.γ i := by ring
  rw [harith]
  exact div_nonneg (mul_nonneg (mul_self_nonneg _) hP) (wp.γ_pos i).le

/-- **Propagation in the flipped frame.** The flipped steady point is monotone in the flipped inducer level.
Mirroring `steadyFam_mono`'s well-founded induction, but in the flipped frame: one level of the recursion is
unfolded with `steadyFam_eq`, the numerators are compared by raising the inducer (`hdrive`) and then raising
the flipped earlier coordinates (`flipProd_mono`, whose physical-nonnegativity and flipped-monotonicity
obligations are the induction hypothesis and `flip_steadyFam_nonneg`), and the shared degradation is
cancelled. `hkind`/`hlen` are the single-input well-formedness facts `flipProd_mono` reads. -/
theorem flip_steadyFam_mono (g : GRN) (hac : g.Acyclic) (σ : String → ℝ) (wp : g.WellPosed) (s : String)
    (hspin : IsSpin σ g) (hbal : Balances σ g) (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (hkind : ∀ op ∈ g.operators, op.kind = .source ∨ op.kind = .receiver ∨ op.kind = .hill1)
    (hlen : ∀ op ∈ g.operators, 2 ≤ op.alphaNums.length)
    (hdrive : FlipDrive g σ wp.inducer s) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (i : g.Species) :
    steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p i
      ≤ steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q i := by
  classical
  have hq : 0 ≤ q := le_trans hp hpq
  refine (g.regulates_wf hac).induction
    (C := fun i => steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p i
      ≤ steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q i) i (fun i ih => ?_)
  -- physical nonnegativity of the fed flipped states
  have hnn : ∀ j, 0 ≤ σ j.1 *
      (if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0) := by
    intro j; by_cases hj : g.regulates j i
    · rw [dif_pos hj]; exact flip_steadyFam_nonneg g hac σ wp s p hp j
    · rw [dif_neg hj, mul_zero]
  have hnn' : ∀ j, 0 ≤ σ j.1 *
      (if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q j else 0) := by
    intro j; by_cases hj : g.regulates j i
    · rw [dif_pos hj]; exact flip_steadyFam_nonneg g hac σ wp s q hq j
    · rw [dif_neg hj, mul_zero]
  -- the induction hypothesis, in the flipped ordering, on `r`-earlier species
  have hle : ∀ j, g.regulates j i →
      (if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0)
      ≤ (if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q j else 0) := by
    intro j hj; rw [dif_pos hj, dif_pos hj]; exact ih j hj
  -- raising the inducer does not lower the production (flipped frame)
  have hstep1 : g.flipProdParam σ wp.inducer s p i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0)
      ≤ g.flipProdParam σ wp.inducer s q i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0) :=
    hdrive i _ p q hpq
  -- raising the flipped earlier coordinates does not lower the production
  have hstep2 : g.flipProdParam σ wp.inducer s q i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0)
      ≤ g.flipProdParam σ wp.inducer s q i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q j else 0) :=
    flipProd_mono g σ (wp.setInducer s q hq) hspin hbal hsigned hkind hlen i
      (y := fun j => if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0)
      (y' := fun j => if _h : g.regulates j i then
        steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q j else 0)
      hnn hnn' hle
  have hnum : g.flipProdParam σ wp.inducer s p i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p j else 0)
      ≤ g.flipProdParam σ wp.inducer s q i
        (fun j => if _h : g.regulates j i then
          steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q j else 0) :=
    le_trans hstep1 hstep2
  rw [steadyFam_eq (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p i,
      steadyFam_eq (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q i,
      div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 (wp.γ_pos i).le)

/-- **The reconvergent dose-response.** Unflipping to the original coordinates: for an acyclic, well-posed,
balanced GRN, the reporter's steady level is monotone in the chosen inducer's level when its spin is `+1`
and antitone when its spin is `-1` — the directional dose-response the sensor certificate promises for a
reconvergent circuit. -/
theorem grn_reconvergent_doseResponse (g : GRN) (hac : g.Acyclic) (σ : String → ℝ) (wp : g.WellPosed)
    (s : String) (reporter : g.Species)
    (hspin : IsSpin σ g) (hbal : Balances σ g) (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (hkind : ∀ op ∈ g.operators, op.kind = .source ∨ op.kind = .receiver ∨ op.kind = .hill1)
    (hlen : ∀ op ∈ g.operators, 2 ≤ op.alphaNums.length)
    (hdrive : FlipDrive g σ wp.inducer s) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (σ reporter.1 = 1 →
      steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p reporter
        ≤ steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q reporter) ∧
    (σ reporter.1 = -1 →
      steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q reporter
        ≤ steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p reporter) := by
  classical
  -- Spin conjugation: the flipped steady value is `σ` times the original steady value.
  have conj : ∀ (u : ℝ) (i : g.Species),
      steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u i
        = σ i.1 * steadyFam (g.regulates_wf hac) wp.γ
            (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u i := by
    intro u i
    refine (g.regulates_wf hac).induction
      (C := fun i => steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u i
        = σ i.1 * steadyFam (g.regulates_wf hac) wp.γ
            (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u i) i (fun i ih => ?_)
    have harg :
        (fun j => σ j.1 * (if _h : g.regulates j i then
            steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0))
          = (fun j => if _h : g.regulates j i then
              steadyFam (g.regulates_wf hac) wp.γ
                (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u j else 0) := by
      funext j
      by_cases hj : g.regulates j i
      · rw [dif_pos hj, dif_pos hj, ih j hj]
        rcases hspin j with h | h <;> rw [h] <;> ring
      · rw [dif_neg hj, dif_neg hj, mul_zero]
    have hF : g.flipProdParam σ wp.inducer s u i
          (fun j => if _h : g.regulates j i then
            steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0)
        = σ i.1 * g.prodOf (inducerAt wp.inducer s u) i
            (fun j => σ j.1 * (if _h : g.regulates j i then
              steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u j else 0)) := rfl
    rw [steadyFam_eq (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) u i,
        steadyFam_eq (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) u i,
        hF, harg]
    ring
  refine ⟨fun hrep => ?_, fun hrep => ?_⟩
  · have hmono := flip_steadyFam_mono g hac σ wp s hspin hbal hsigned hkind hlen hdrive hp hpq reporter
    rw [conj p reporter, conj q reporter, hrep] at hmono
    linarith
  · have hmono := flip_steadyFam_mono g hac σ wp s hspin hbal hsigned hkind hlen hdrive hp hpq reporter
    rw [conj p reporter, conj q reporter, hrep] at hmono
    linarith

/-- The balancing spin as a real-valued function on species names, read off the monotonicity
certificate: the `±1` assignment `spinAssignment` builds over the signed interaction graph, cast to `ℝ`. -/
noncomputable def grnSpin (g : GRN) : String → ℝ :=
  fun v => ((spinAssignment (signedInteractionGraph g) v : Int) : ℝ)

/-- On a graph-monotone GRN the balancing spin takes values `±1` on every regulated species: a vertex of
the signed interaction graph is `±1` by `spinAssignment_mem`, and off the graph `spinAssignment` is its
default `1`. -/
theorem grnSpin_isSpin (g : GRN) (h : isMonotone g = true) : IsSpin (grnSpin g) g := by
  unfold isMonotone at h
  intro i
  have hpm : spinAssignment (signedInteractionGraph g) i.1 = 1 ∨
      spinAssignment (signedInteractionGraph g) i.1 = -1 := by
    by_cases hv : i.1 ∈ verticesOf (signedInteractionGraph g)
    · exact spinAssignment_mem (signedInteractionGraph g) h hv
    · unfold spinAssignment
      split
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inl rfl
  simp only [grnSpin]
  rcases hpm with h1 | h1 <;> rw [h1]
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)

/-- On a graph-monotone GRN the balancing spin balances the signed interaction graph: each edge
`(j, i, s)` satisfies `grnSpin i = s · grnSpin j`, the real-valued cast of `balance`. -/
theorem grnSpin_balances (g : GRN) (h : isMonotone g = true) : Balances (grnSpin g) g := by
  unfold isMonotone at h
  intro e he
  have hb := balance (signedInteractionGraph g) h he
  simp only [grnSpin]
  rw [hb]
  push_cast
  ring

/-- **The reconvergent dose-response from the certificate alone.** For an acyclic, well-posed,
graph-monotone GRN the balancing spin `grnSpin g` is constructed from the certificate, so its spin and
balance obligations are discharged automatically: the reporter's steady level is monotone in the chosen
inducer's level when `grnSpin g reporter = 1` and antitone when `grnSpin g reporter = -1`. -/
theorem grn_reconvergent_doseResponse_of_monotone (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed)
    (s : String) (reporter : g.Species) (hmono : isMonotone g = true)
    (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (hkind : ∀ op ∈ g.operators, op.kind = .source ∨ op.kind = .receiver ∨ op.kind = .hill1)
    (hlen : ∀ op ∈ g.operators, 2 ≤ op.alphaNums.length)
    (hdrive : FlipDrive g (grnSpin g) wp.inducer s) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (grnSpin g reporter.1 = 1 →
      steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p reporter
        ≤ steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q reporter) ∧
    (grnSpin g reporter.1 = -1 →
      steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q reporter
        ≤ steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p reporter) :=
  grn_reconvergent_doseResponse g hac (grnSpin g) wp s reporter
    (grnSpin_isSpin g hmono) (grnSpin_balances g hmono) hsigned hkind hlen hdrive hp hpq

end GRN
