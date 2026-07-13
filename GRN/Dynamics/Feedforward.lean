import Mathlib

/-!
# Tier 2 — the feedforward IR and its unique steady state

A `FeedforwardSystem` is the intermediate representation the sensor functor targets: a type of species
`ι` with a **well-founded** "is-regulated-by" relation `r`, each species produced only from `r`-earlier
species, with positive degradation. `local'` — species `i`'s production reads only `r`-earlier coordinates
— is the entire feedforward content and exactly what forward substitution needs.

Indexing by a well-founded relation rather than `Fin n` is deliberate: the interaction graph's regulation
relation is well-founded precisely when the circuit is acyclic, so a sensor GRN instantiates this IR
directly — no topological sort or `Fin n` reindexing required.

The steady state (where the assembled field `prodᵢ − γᵢ·xᵢ` vanishes) is **unique and constructive**:
solved species by species down the well-founded order, with no Fréchet derivatives, P-matrices, or
fixed-point theorems (see `notes/functor-plan.md`).
-/

namespace GRN.Dynamics

open scoped Classical

variable {ι : Type*} {r : ι → ι → Prop}

/-- **Acyclic ⟹ well-founded** for a finite regulation relation: if no species transitively regulates
itself, the relation is well-founded, so a sensor GRN instantiates `FeedforwardSystem` directly — this is
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

/-- **The feedforward sensor has a unique steady state** — constructively. -/
theorem exists_unique_steady (S : FeedforwardSystem ι r) : ∃! x, S.IsSteady x :=
  ⟨S.steadyPoint, S.steadyPoint_isSteady, fun _ hy => S.steady_unique hy S.steadyPoint_isSteady⟩

/-- The steady state is nonnegative — by induction down the regulation order. -/
theorem steadyPoint_nonneg (S : FeedforwardSystem ι r) (i : ι) : 0 ≤ S.steadyPoint i := by
  refine S.wf.induction (C := fun i => 0 ≤ S.steadyPoint i) i (fun i ih => ?_)
  rw [steadyPoint_eq]
  refine div_nonneg (S.nonneg i _ (fun j => ?_)) (S.hγ i).le
  by_cases hj : r j i
  · rw [dif_pos hj]; exact ih j hj
  · simp [dif_neg hj]

/-- **Monotone comparison of steady states** — the dose-response monotonicity engine (T2). If two systems
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

end GRN.Dynamics
