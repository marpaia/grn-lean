import Mathlib

/-!
# The feedforward IR and its unique steady state

A `FeedforwardSystem` is the intermediate representation the sensor functor targets: a type of species
`ι` with a **well-founded** "is-regulated-by" relation `r`, each species produced only from `r`-earlier
species, with positive degradation. `local'` (species `i`'s production reads only `r`-earlier coordinates)
is the entire feedforward content and exactly what forward substitution needs.

Indexing by a well-founded relation rather than `Fin n` is deliberate: the interaction graph's regulation
relation is well-founded precisely when the circuit is acyclic, so a sensor GRN instantiates this IR
directly, with no topological sort or `Fin n` reindexing required.

The steady state (where the assembled field `prodᵢ − γᵢ·xᵢ` vanishes) is **unique and constructive**:
solved by forward substitution species by species down the well-founded order, with no Fréchet
derivatives, P-matrices, or fixed-point theorems.
-/

namespace GRN.Dynamics

open scoped Classical

variable {ι : Type*} {r : ι → ι → Prop}

/-- **Acyclic ⟹ well-founded** for a finite regulation relation: if no species transitively regulates
itself, the relation is well-founded, so a sensor GRN instantiates `FeedforwardSystem` directly. This is
what replaces a topological sort. -/
theorem wellFounded_of_acyclic [Finite ι] (h : ∀ i, ¬ Relation.TransGen r i i) : WellFounded r := by
  haveI : Std.Irrefl (Relation.TransGen r) := ⟨h⟩
  haveI : IsTrans ι (Relation.TransGen r) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  exact Subrelation.wf (fun hr => Relation.TransGen.single hr)
    (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r))

/-- A feedforward assembled system: species `ι`, a well-founded regulation relation `r`, positive
degradation, and production reading only `r`-earlier species. -/
structure FeedforwardSystem (ι : Type*) (r : ι → ι → Prop) where
  /-- The regulation relation is well-founded (equivalently, the circuit is acyclic). -/
  wf : WellFounded r
  /-- Degradation + dilution rate of each species. -/
  γ : ι → ℝ
  /-- Degradation is strictly positive. -/
  hγ : ∀ i, 0 < γ i
  /-- Production rate of each species as a function of the full state. -/
  prod : ι → (ι → ℝ) → ℝ
  /-- Feedforward locality: species `i`'s production depends only on `r`-earlier species. -/
  local' : ∀ i x y, (∀ j, r j i → x j = y j) → prod i x = prod i y
  /-- Production is nonnegative on nonnegative states. -/
  nonneg : ∀ i x, (∀ j, 0 ≤ x j) → 0 ≤ prod i x

namespace FeedforwardSystem

/-- A steady state: the assembled field `prodᵢ − γᵢ·xᵢ` vanishes in every coordinate. -/
def IsSteady (S : FeedforwardSystem ι r) (x : ι → ℝ) : Prop :=
  ∀ i, S.prod i x = S.γ i * x i

/-- Steady states are unique: well-founded induction over the regulation order, cancelling `γ`. -/
theorem steady_unique (S : FeedforwardSystem ι r) {x y : ι → ℝ}
    (hx : S.IsSteady x) (hy : S.IsSteady y) : x = y := by
  funext i
  refine S.wf.induction (C := fun i => x i = y i) i (fun i ih => ?_)
  have hpe : S.prod i x = S.prod i y := S.local' i x y (fun j hj => ih j hj)
  have key : S.γ i * x i = S.γ i * y i := by rw [← hx i, hpe, hy i]
  exact mul_left_cancel₀ (S.hγ i).ne' key

/-- The recursion functional: species `i`'s value from those of `r`-earlier species. -/
noncomputable def steadyF (S : FeedforwardSystem ι r) (i : ι) (rec : ∀ j, r j i → ℝ) : ℝ :=
  S.prod i (fun j => if h : r j i then rec j h else 0) / S.γ i

/-- The steady state, by forward substitution over the well-founded order. -/
noncomputable def steadyPoint (S : FeedforwardSystem ι r) : ι → ℝ := S.wf.fix S.steadyF

theorem steadyPoint_eq (S : FeedforwardSystem ι r) (i : ι) :
    S.steadyPoint i = S.prod i (fun j => if _h : r j i then S.steadyPoint j else 0) / S.γ i := by
  unfold steadyPoint steadyF
  rw [WellFounded.fix_eq]

/-- The forward-substitution point is a steady state. -/
theorem prod_steadyPoint (S : FeedforwardSystem ι r) (i : ι) :
    S.prod i S.steadyPoint = S.γ i * S.steadyPoint i := by
  have hpe : S.prod i (fun j => if h : r j i then S.steadyPoint j else 0) = S.prod i S.steadyPoint :=
    S.local' i _ _ (fun j hj => dif_pos hj)
  have h1 : S.steadyPoint i = S.prod i S.steadyPoint / S.γ i := by rw [steadyPoint_eq, hpe]
  have h2 : S.prod i S.steadyPoint = S.steadyPoint i * S.γ i := (div_eq_iff (S.hγ i).ne').mp h1.symm
  rw [h2, mul_comm]

theorem steadyPoint_isSteady (S : FeedforwardSystem ι r) : S.IsSteady S.steadyPoint :=
  fun i => S.prod_steadyPoint i

/-- **The feedforward sensor has a unique steady state**, constructively. -/
theorem exists_unique_steady (S : FeedforwardSystem ι r) : ∃! x, S.IsSteady x :=
  ⟨S.steadyPoint, S.steadyPoint_isSteady, fun _ hy => S.steady_unique hy S.steadyPoint_isSteady⟩

/-- The steady state is nonnegative, by induction down the regulation order. -/
theorem steadyPoint_nonneg (S : FeedforwardSystem ι r) (i : ι) : 0 ≤ S.steadyPoint i := by
  refine S.wf.induction (C := fun i => 0 ≤ S.steadyPoint i) i (fun i ih => ?_)
  rw [steadyPoint_eq]
  refine div_nonneg (S.nonneg i _ (fun j => ?_)) (S.hγ i).le
  by_cases hj : r j i
  · rw [dif_pos hj]; exact ih j hj
  · simp [dif_neg hj]

/-- **Monotone comparison of steady states**: the dose-response monotonicity engine (T2). If two systems
share degradation, the second's production dominates the first's on nonnegative states, and the second's
production is monotone in `r`-earlier species, then the second's steady state dominates coordinatewise. -/
theorem steady_le (S T : FeedforwardSystem ι r) (hγ : ∀ i, S.γ i = T.γ i)
    (hmonoT : ∀ i x y, (∀ j, 0 ≤ x j) → (∀ j, 0 ≤ y j) → (∀ j, r j i → x j ≤ y j) →
      T.prod i x ≤ T.prod i y)
    (hdom : ∀ i x, (∀ j, 0 ≤ x j) → S.prod i x ≤ T.prod i x) :
    ∀ i, S.steadyPoint i ≤ T.steadyPoint i := by
  intro i
  refine S.wf.induction (C := fun i => S.steadyPoint i ≤ T.steadyPoint i) i (fun i ih => ?_)
  have hchain : S.prod i S.steadyPoint ≤ T.prod i T.steadyPoint :=
    le_trans (hdom i S.steadyPoint S.steadyPoint_nonneg)
      (hmonoT i S.steadyPoint T.steadyPoint S.steadyPoint_nonneg T.steadyPoint_nonneg
        (fun j hj => ih j hj))
  rw [S.prod_steadyPoint i, T.prod_steadyPoint i, hγ i] at hchain
  exact le_of_mul_le_mul_left hchain (T.hγ i)

end FeedforwardSystem

/-! ## Continuity of the steady state in a parameter

For dose-response and EC50 we need the steady state as a function of the inducer level. Modelling the
inducer as a parameter `p` entering the production, `steadyFam` is the forward-substitution steady point
with a parameterized production, and `steadyFam_continuous` shows it is continuous in `p`. The proof is
well-founded induction on the species using the recursion's own defining equation (`steadyFam_eq`); there
is no appeal to a general continuity theorem for `WellFounded.fix`. -/

/-- The forward-substitution steady point with a **parameterized** production: fixed relation, well-founded
order, and degradation, with production depending on a parameter `p` (e.g. the inducer level). -/
noncomputable def steadyFam {P : Type*} (wf : WellFounded r) (γ : ι → ℝ)
    (prod : P → ι → (ι → ℝ) → ℝ) (p : P) : ι → ℝ :=
  wf.fix (fun i rec => prod p i (fun j => if h : r j i then rec j h else 0) / γ i)

theorem steadyFam_eq {P : Type*} (wf : WellFounded r) (γ : ι → ℝ) (prod : P → ι → (ι → ℝ) → ℝ)
    (p : P) (i : ι) :
    steadyFam wf γ prod p i
      = prod p i (fun j => if _h : r j i then steadyFam wf γ prod p j else 0) / γ i := by
  unfold steadyFam
  rw [WellFounded.fix_eq]

/-- **The steady state is continuous in the parameter.** If the production is jointly continuous in the
parameter and the state, then `p ↦ steadyFam … p i` is continuous, by well-founded induction on `i`,
rewriting one level with `steadyFam_eq` and propagating continuity through the (finite or infinite) state
vector coordinatewise. -/
theorem steadyFam_continuous {P : Type*} [TopologicalSpace P] (wf : WellFounded r) (γ : ι → ℝ)
    {prod : P → ι → (ι → ℝ) → ℝ}
    (hprod : ∀ i, Continuous fun q : P × (ι → ℝ) => prod q.1 i q.2) (i : ι) :
    Continuous fun p => steadyFam wf γ prod p i := by
  refine wf.induction (C := fun i => Continuous fun p => steadyFam wf γ prod p i) i (fun i ih => ?_)
  have hstate : Continuous fun p : P =>
      (fun j => if _h : r j i then steadyFam wf γ prod p j else 0 : ι → ℝ) := by
    rw [continuous_pi_iff]
    intro j
    by_cases h : r j i
    · simp only [dif_pos h]; exact ih j h
    · simp only [dif_neg h]; exact continuous_const
  have heq : (fun p => steadyFam wf γ prod p i)
      = fun p => prod p i (fun j => if _h : r j i then steadyFam wf γ prod p j else 0) / γ i := by
    funext p; exact steadyFam_eq wf γ prod p i
  rw [heq]
  exact ((hprod i).comp (continuous_id.prodMk hstate)).div_const (γ i)

/-- The parameterized steady state is nonnegative when production is nonnegative on nonnegative states. -/
theorem steadyFam_nonneg {P : Type*} (wf : WellFounded r) {γ : ι → ℝ} (hγ : ∀ i, 0 < γ i)
    {prod : P → ι → (ι → ℝ) → ℝ} (p : P) (hnn : ∀ i x, (∀ j, 0 ≤ x j) → 0 ≤ prod p i x) (i : ι) :
    0 ≤ steadyFam wf γ prod p i := by
  refine wf.induction (C := fun i => 0 ≤ steadyFam wf γ prod p i) i (fun i ih => ?_)
  rw [steadyFam_eq]
  refine div_nonneg (hnn i _ (fun j => ?_)) (hγ i).le
  by_cases hj : r j i
  · rw [dif_pos hj]; exact ih j hj
  · simp [dif_neg hj]

/-- **Continuity of the steady state on the nonnegative orthant.** The `ContinuousOn` refinement of
`steadyFam_continuous`, for productions (like Hill kinetics) continuous only where the parameter and state
are nonnegative: if production is nonnegative and jointly continuous on `[0,∞) × (nonneg states)`, then
`u ↦ steadyFam … u i` is continuous on `[0,∞)`. Same WF induction, tracking that the state stays in the
nonnegative orthant. -/
theorem steadyFam_continuousOn (wf : WellFounded r) (γ : ι → ℝ) (hγ : ∀ i, 0 < γ i)
    {prod : ℝ → ι → (ι → ℝ) → ℝ}
    (hnn : ∀ t ∈ Set.Ici (0 : ℝ), ∀ k x, (∀ l, 0 ≤ x l) → 0 ≤ prod t k x)
    (hprod : ∀ i, ContinuousOn (fun v : ℝ × (ι → ℝ) => prod v.1 i v.2)
      (Set.Ici 0 ×ˢ Set.univ.pi (fun _ => Set.Ici 0)))
    (i : ι) : ContinuousOn (fun u => steadyFam wf γ prod u i) (Set.Ici 0) := by
  refine wf.induction (C := fun i => ContinuousOn (fun u => steadyFam wf γ prod u i) (Set.Ici 0))
    i (fun i ih => ?_)
  have hstate : ContinuousOn
      (fun u : ℝ => (fun l => if _h : r l i then steadyFam wf γ prod u l else 0 : ι → ℝ)) (Set.Ici 0) := by
    rw [continuousOn_pi]
    intro l
    by_cases hl : r l i
    · simp only [dif_pos hl]; exact ih l hl
    · simp only [dif_neg hl]; exact continuousOn_const
  have hmaps : Set.MapsTo
      (fun u : ℝ => (u, (fun l => if _h : r l i then steadyFam wf γ prod u l else 0 : ι → ℝ)))
      (Set.Ici 0) (Set.Ici 0 ×ˢ Set.univ.pi (fun _ => Set.Ici 0)) := by
    intro u hu
    refine Set.mem_prod.2 ⟨hu, Set.mem_univ_pi.2 (fun l => ?_)⟩
    simp only [Set.mem_Ici]
    by_cases hl : r l i
    · rw [dif_pos hl]; exact steadyFam_nonneg wf hγ u (fun k x h => hnn u hu k x h) l
    · simp [dif_neg hl]
  have hcomp : ContinuousOn
      (fun u => prod u i (fun l => if _h : r l i then steadyFam wf γ prod u l else 0)) (Set.Ici 0) :=
    (hprod i).comp (continuousOn_id.prodMk hstate) hmaps
  have heq : (fun u => steadyFam wf γ prod u i)
      = fun u => prod u i (fun l => if _h : r l i then steadyFam wf γ prod u l else 0) / γ i := by
    funext u; exact steadyFam_eq wf γ prod u i
  rw [heq]
  exact hcomp.div_const (γ i)

/-- **The steady state is monotone in the parameter** (the dose-response monotonicity engine through the
real `steadyPoint`): if raising the parameter does not lower any production, and the higher parameter's
production is monotone in `r`-earlier species, then `steadyFam … p i ≤ steadyFam … q i`, by well-founded
induction, cancelling the shared degradation. -/
theorem steadyFam_mono {P : Type*} (wf : WellFounded r) {γ : ι → ℝ} (hγ : ∀ i, 0 < γ i)
    {prod : P → ι → (ι → ℝ) → ℝ} {p q : P}
    (hnnp : ∀ i x, (∀ j, 0 ≤ x j) → 0 ≤ prod p i x)
    (hnnq : ∀ i x, (∀ j, 0 ≤ x j) → 0 ≤ prod q i x)
    (hstep : ∀ i x, (∀ j, 0 ≤ x j) → prod p i x ≤ prod q i x)
    (hmonoq : ∀ i x y, (∀ j, 0 ≤ x j) → (∀ j, 0 ≤ y j) →
      (∀ j, r j i → x j ≤ y j) → prod q i x ≤ prod q i y) (i : ι) :
    steadyFam wf γ prod p i ≤ steadyFam wf γ prod q i := by
  refine wf.induction (C := fun i => steadyFam wf γ prod p i ≤ steadyFam wf γ prod q i) i (fun i ih => ?_)
  have hpnn : ∀ j, 0 ≤ (if _h : r j i then steadyFam wf γ prod p j else 0) := by
    intro j; by_cases hj : r j i
    · rw [dif_pos hj]; exact steadyFam_nonneg wf hγ p hnnp j
    · simp [dif_neg hj]
  have hqnn : ∀ j, 0 ≤ (if _h : r j i then steadyFam wf γ prod q j else 0) := by
    intro j; by_cases hj : r j i
    · rw [dif_pos hj]; exact steadyFam_nonneg wf hγ q hnnq j
    · simp [dif_neg hj]
  have hnum : prod p i (fun j => if _h : r j i then steadyFam wf γ prod p j else 0)
      ≤ prod q i (fun j => if _h : r j i then steadyFam wf γ prod q j else 0) :=
    le_trans (hstep i _ hpnn) (hmonoq i _ _ hpnn hqnn (fun j hj => by
      rw [dif_pos hj, dif_pos hj]; exact ih j hj))
  rw [steadyFam_eq wf γ prod p i, steadyFam_eq wf γ prod q i, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 (hγ i).le)

/-! ### Strict monotonicity: the EC50-uniqueness engine

For a *unique* EC50 the reporter's dose-response must be injective, i.e. strictly monotone in the inducer.
Strictness enters at a species that directly feels the parameter (`steadyFam_lt_base`) and propagates along
any strictly-monotone regulation step (`steadyFam_lt_step`): with the whole state weakly rising (from
`steadyFam_mono`) and one regulator strictly rising, a production strictly monotone in that regulator
strictly rises. Chaining a base and steps from the inducer to the reporter yields the reporter's strict
dose-response; `StrictMonoOn` then feeds `steadyFam_ec50`. -/

/-- Strictness at a species that directly feels the parameter: if raising the parameter *strictly* raises
this species' production, it strictly raises its steady value. -/
theorem steadyFam_lt_base (wf : WellFounded r) {γ : ι → ℝ} (hγ : ∀ i, 0 < γ i)
    {prod : ℝ → ι → (ι → ℝ) → ℝ} {p q : ℝ} {i : ι}
    (hnnp : ∀ k x, (∀ l, 0 ≤ x l) → 0 ≤ prod p k x)
    (hnnq : ∀ k x, (∀ l, 0 ≤ x l) → 0 ≤ prod q k x)
    (hle : ∀ k, steadyFam wf γ prod p k ≤ steadyFam wf γ prod q k)
    (hmonoq : ∀ x y, (∀ l, 0 ≤ x l) → (∀ l, 0 ≤ y l) →
      (∀ l, r l i → x l ≤ y l) → prod q i x ≤ prod q i y)
    (hstrict : ∀ x, (∀ l, 0 ≤ x l) → prod p i x < prod q i x) :
    steadyFam wf γ prod p i < steadyFam wf γ prod q i := by
  have hpnn : ∀ l, 0 ≤ (if _h : r l i then steadyFam wf γ prod p l else 0) := by
    intro l; by_cases hl : r l i
    · rw [dif_pos hl]; exact steadyFam_nonneg wf hγ p hnnp l
    · simp [dif_neg hl]
  have hqnn : ∀ l, 0 ≤ (if _h : r l i then steadyFam wf γ prod q l else 0) := by
    intro l; by_cases hl : r l i
    · rw [dif_pos hl]; exact steadyFam_nonneg wf hγ q hnnq l
    · simp [dif_neg hl]
  have hstle : ∀ l, r l i → (if _h : r l i then steadyFam wf γ prod p l else 0)
      ≤ (if _h : r l i then steadyFam wf γ prod q l else 0) := by
    intro l hl; rw [dif_pos hl, dif_pos hl]; exact hle l
  have hnum : prod p i (fun l => if _h : r l i then steadyFam wf γ prod p l else 0)
      < prod q i (fun l => if _h : r l i then steadyFam wf γ prod q l else 0) :=
    lt_of_lt_of_le (hstrict _ hpnn) (hmonoq _ _ hpnn hqnn hstle)
  rw [steadyFam_eq wf γ prod p i, steadyFam_eq wf γ prod q i, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hnum (inv_pos.2 (hγ i))

/-- Strict propagation: if a regulator `j` of `i` strictly rises, the parameter does not lower `i`'s
production, and `i`'s production strictly rises in coordinate `j`, then `i`'s steady value strictly rises. -/
theorem steadyFam_lt_step (wf : WellFounded r) {γ : ι → ℝ} (hγ : ∀ i, 0 < γ i)
    {prod : ℝ → ι → (ι → ℝ) → ℝ} {p q : ℝ} {i j : ι} (hrij : r j i)
    (hnnp : ∀ k x, (∀ l, 0 ≤ x l) → 0 ≤ prod p k x)
    (hnnq : ∀ k x, (∀ l, 0 ≤ x l) → 0 ≤ prod q k x)
    (hle : ∀ k, steadyFam wf γ prod p k ≤ steadyFam wf γ prod q k)
    (hstep : ∀ x, (∀ l, 0 ≤ x l) → prod p i x ≤ prod q i x)
    (hstrictq : ∀ x y, (∀ l, 0 ≤ x l) → (∀ l, 0 ≤ y l) →
      (∀ l, x l ≤ y l) → x j < y j → prod q i x < prod q i y)
    (hlt : steadyFam wf γ prod p j < steadyFam wf γ prod q j) :
    steadyFam wf γ prod p i < steadyFam wf γ prod q i := by
  have hpnn : ∀ l, 0 ≤ (if _h : r l i then steadyFam wf γ prod p l else 0) := by
    intro l; by_cases hl : r l i
    · rw [dif_pos hl]; exact steadyFam_nonneg wf hγ p hnnp l
    · simp [dif_neg hl]
  have hqnn : ∀ l, 0 ≤ (if _h : r l i then steadyFam wf γ prod q l else 0) := by
    intro l; by_cases hl : r l i
    · rw [dif_pos hl]; exact steadyFam_nonneg wf hγ q hnnq l
    · simp [dif_neg hl]
  have hstle : ∀ l, (if _h : r l i then steadyFam wf γ prod p l else 0)
      ≤ (if _h : r l i then steadyFam wf γ prod q l else 0) := by
    intro l; by_cases hl : r l i
    · rw [dif_pos hl, dif_pos hl]; exact hle l
    · rw [dif_neg hl, dif_neg hl]
  have hstlt : (if _h : r j i then steadyFam wf γ prod p j else 0)
      < (if _h : r j i then steadyFam wf γ prod q j else 0) := by
    rw [dif_pos hrij, dif_pos hrij]; exact hlt
  have hnum : prod p i (fun l => if _h : r l i then steadyFam wf γ prod p l else 0)
      < prod q i (fun l => if _h : r l i then steadyFam wf γ prod q l else 0) :=
    lt_of_le_of_lt (hstep _ hpnn) (hstrictq _ _ hpnn hqnn hstle hstlt)
  rw [steadyFam_eq wf γ prod p i, steadyFam_eq wf γ prod q i, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right hnum (inv_pos.2 (hγ i))

end GRN.Dynamics
