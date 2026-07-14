import Mathlib
import GRN.Certificate

/-!
# The balancing spin witness

The sensor certificate `isMonotoneEdges` checks *sign-consistency* of the signed interaction graph by a
relaxation (`colorable`): it assigns each vertex a spin `±1` so that every edge's sign is the product of
its endpoints' spins. This module exposes that relaxation assignment as a function `σ : String → Int` and
records its defining property, `balance`: on a sign-consistent graph every edge `(j, i, s)` satisfies
`σ i = s · σ j`.

The balancing spin is the data the reconvergent-sensor argument in `GRN.Dynamics.ReconvergentSensor`
consumes: it defines the flipped coordinates `y_i = σ_i · x_i` in which a sign-consistent (mixed
activation/repression) network becomes cooperative (monotone increasing) and the dose-response
monotonicity engine applies.
-/

namespace GRN

/-- The fixed-point spin assignment `colorable` builds: seed one still-unassigned vertex per connected
component with spin `+1`, relax to a `relaxToFix` fixed point, and repeat until every vertex is covered
(or a sign-consistency contradiction stops the relaxation). This is exactly the list `colorable` walks;
`colorable` returns only the `Bool` verdict, so we reconstruct the assignment itself as data. -/
def spinFix (edges : List SignedEdge) : List (String × Int) :=
  let rec go (fuel : Nat) (spin : List (String × Int)) : List (String × Int) :=
    match fuel with
    | 0 => spin
    | fuel + 1 =>
      match relaxToFix edges spin with
      | none => spin
      | some sp =>
        match (verticesOf edges).find? (fun v => (spinOf sp v).isNone) with
        | none => sp
        | some v => go fuel ((v, 1) :: sp)
  go ((verticesOf edges).length + 1) []

/-- The balancing spin assignment `σ : String → Int` read off `colorable`'s relaxation (`spinFix`),
coerced to a genuine `±1` value at every vertex (the sign of the relaxed spin, defaulting to `+1` on an
unrelaxed vertex). -/
noncomputable def spinAssignment (edges : List SignedEdge) : String → Int :=
  fun v =>
    match spinOf (spinFix edges) v with
    | some x => if 0 ≤ x then 1 else -1
    | none => 1

/-- On a sign-consistent graph the balancing spin takes values in `{±1}` at every vertex. -/
theorem spinAssignment_mem (edges : List SignedEdge) (h : isMonotoneEdges edges = true)
    {v : String} (hv : v ∈ verticesOf edges) :
    spinAssignment edges v = 1 ∨ spinAssignment edges v = -1 := by
  unfold spinAssignment
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

/-! ### Machinery for `balance`

The relaxation `spinFix` builds the `±1` assignment; `balance` records that it balances every edge.
The proof rests on: (1) all assigned values are `±1`; (2) a successful relaxation reaches a genuine
fixed point (a fuel-measure argument), which certifies `vb = s·va` on every both-assigned edge; and
(3) completeness — under `colorable` every vertex is assigned, so both endpoints of every edge are. -/

/-- The single-edge propagation step folded by `relaxPass`. -/
private def stepf (st : Option (List (String × Int) × Bool)) (e : SignedEdge) :
    Option (List (String × Int) × Bool) :=
  match st with
  | none => none
  | some (sp, changed) =>
      let a := e.1; let b := e.2.1; let s := e.2.2
      match spinOf sp a, spinOf sp b with
      | some va, some vb => if vb == s * va then some (sp, changed) else none
      | some va, none => some ((b, s * va) :: sp, true)
      | none, some vb => some ((a, s * vb) :: sp, true)
      | none, none => some (sp, changed)

private theorem relaxPass_eq (edges : List SignedEdge) (spin : List (String × Int)) :
    relaxPass edges spin = edges.foldl stepf (some (spin, false)) := by
  unfold relaxPass stepf; rfl

private theorem spinOf_cons (k : String) (x : Int) (sp : List (String × Int)) (w : String) :
    spinOf ((k, x) :: sp) w = if k == w then some x else spinOf sp w := by
  unfold spinOf
  simp only [List.find?_cons]
  cases h : (k == w) <;> simp [h]

private theorem spinOf_cons_self (k : String) (x : Int) (sp : List (String × Int)) :
    spinOf ((k, x) :: sp) k = some x := by
  rw [spinOf_cons, if_pos (by simp)]

private theorem spinOf_cons_mono (k : String) (x : Int) (sp : List (String × Int))
    (hk : spinOf sp k = none) {w : String} {y : Int} (hy : spinOf sp w = some y) :
    spinOf ((k, x) :: sp) w = some y := by
  rw [spinOf_cons]
  by_cases hkw : k = w
  · subst hkw; rw [hk] at hy; exact absurd hy (by simp)
  · rw [if_neg (by simp only [beq_iff_eq]; exact hkw)]; exact hy

private theorem foldl_stepf_none (l : List SignedEdge) : l.foldl stepf none = none := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.foldl_cons, show stepf none a = none from rfl]; exact ih

/-- A pass started from `changed = true` ends `changed = true` (or fails). -/
private theorem foldl_changed_true :
    ∀ (es : List SignedEdge) (sp sp' : List (String × Int)) (b' : Bool),
      es.foldl stepf (some (sp, true)) = some (sp', b') → b' = true := by
  intro es
  induction es with
  | nil => intro sp sp' b' h; simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  | cons e rest ih =>
    intro sp sp' b' h
    rw [List.foldl_cons] at h
    rcases hla : spinOf sp e.1 with _ | va <;> rcases hlb : spinOf sp e.2.1 with _ | vb <;>
      simp only [stepf, hla, hlb] at h
    · exact ih _ _ _ h
    · exact ih _ _ _ h
    · exact ih _ _ _ h
    · by_cases hc : (vb == e.2.2 * va) = true
      · rw [if_pos hc] at h; exact ih _ _ _ h
      · rw [if_neg hc, foldl_stepf_none] at h; exact absurd h (by simp)

/-- Generic monotonicity of `countP` under a pointwise-weaker predicate. -/
private theorem countP_mono {α} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, q x = true → p x = true) : l.countP q ≤ l.countP p := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons]
    have ht : ∀ x ∈ t, q x = true → p x = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hrec := ih ht
    by_cases hq : q a = true
    · have hp : p a = true := h a (List.mem_cons_self) hq
      simp only [hq, hp, if_true]; omega
    · simp only [Bool.not_eq_true] at hq
      simp only [hq, Bool.false_eq_true, if_false, Nat.add_zero]
      by_cases hp : p a = true <;> simp only [hp, if_true, Bool.not_eq_true] at * <;> omega

/-- Strict `countP` decrease from a witness that flips from counted to not-counted. -/
private theorem countP_strict {α} (l : List α) (p q : α → Bool)
    (hle : ∀ x ∈ l, q x = true → p x = true)
    (hex : ∃ x ∈ l, p x = true ∧ q x = false) : l.countP q < l.countP p := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hex; simp at hx
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons]
    have hlet : ∀ x ∈ t, q x = true → p x = true := fun x hx => hle x (List.mem_cons_of_mem _ hx)
    obtain ⟨x0, hx0, hpx0, hqx0⟩ := hex
    rcases List.mem_cons.1 hx0 with rfl | hx0t
    · have hmono := countP_mono t p q hlet
      simp only [hqx0, hpx0, Bool.false_eq_true, if_false, if_true]; omega
    · have hstrict := ih hlet ⟨x0, hx0t, hpx0, hqx0⟩
      by_cases hqa : q a = true
      · have hpa : p a = true := hle a (List.mem_cons_self) hqa
        simp only [hqa, hpa, if_true]; omega
      · simp only [Bool.not_eq_true] at hqa
        simp only [hqa, Bool.false_eq_true, if_false, Nat.add_zero]
        by_cases hpa : p a = true <;> simp only [hpa, if_true] <;> omega

/-- One `relaxPass` fold: it only extends the assignment (mono), preserves `±1`-valuedness (pm), and
if it changes anything then some edge went from a free endpoint to both-assigned (witness). -/
private theorem foldMain :
    ∀ (es : List SignedEdge) (sp0 : List (String × Int)) (b0 : Bool)
      (sp' : List (String × Int)) (ch : Bool),
      (∀ e ∈ es, e.2.2 = 1 ∨ e.2.2 = -1) →
      es.foldl stepf (some (sp0, b0)) = some (sp', ch) →
      (∀ w y, spinOf sp0 w = some y → spinOf sp' w = some y) ∧
      ((∀ w y, spinOf sp0 w = some y → y = 1 ∨ y = -1) →
        (∀ w y, spinOf sp' w = some y → y = 1 ∨ y = -1)) ∧
      (b0 = false → ch = true →
        ∃ e0 ∈ es, ((spinOf sp0 e0.1).isNone = true ∨ (spinOf sp0 e0.2.1).isNone = true) ∧
          (spinOf sp' e0.1).isSome = true ∧ (spinOf sp' e0.2.1).isSome = true) := by
  intro es
  induction es with
  | nil =>
    intro sp0 b0 sp' ch _ hfold
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at hfold
    obtain ⟨rfl, rfl⟩ := hfold
    refine ⟨fun w y hy => hy, fun hpm w y hy => hpm w y hy, ?_⟩
    intro hb0 hch; rw [hb0] at hch; exact absurd hch (by simp)
  | cons e rest ih =>
    intro sp0 b0 sp' ch hsigns hfold
    rw [List.foldl_cons] at hfold
    have hse : e.2.2 = 1 ∨ e.2.2 = -1 := hsigns e List.mem_cons_self
    have hsrest : ∀ e' ∈ rest, e'.2.2 = 1 ∨ e'.2.2 = -1 :=
      fun e' h => hsigns e' (List.mem_cons_of_mem _ h)
    rcases hla : spinOf sp0 e.1 with _ | va <;> rcases hlb : spinOf sp0 e.2.1 with _ | vb <;>
      simp only [stepf, hla, hlb] at hfold
    · -- none, none : no change
      obtain ⟨m0, p0, w0⟩ := ih sp0 b0 sp' ch hsrest hfold
      refine ⟨m0, p0, ?_⟩
      intro hb0 hch
      obtain ⟨e0, he0, hc, hs1, hs2⟩ := w0 hb0 hch
      exact ⟨e0, List.mem_cons_of_mem _ he0, hc, hs1, hs2⟩
    · -- none, some vb : assign e.1
      set sp1 := (e.1, e.2.2 * vb) :: sp0 with hsp1
      obtain ⟨m1, p1, _⟩ := ih sp1 true sp' ch hsrest hfold
      have hmp : ∀ w y, spinOf sp0 w = some y → spinOf sp1 w = some y :=
        fun w y hy => spinOf_cons_mono _ _ _ hla hy
      refine ⟨fun w y hy => m1 w y (hmp w y hy), ?_, ?_⟩
      · intro hpm0 w y hy
        refine p1 ?_ w y hy
        intro w' y' hy'
        rw [hsp1, spinOf_cons] at hy'
        by_cases hkw : e.1 = w'
        · subst hkw; rw [if_pos (by simp)] at hy'; injection hy' with hy'; subst hy'
          rcases hse with h | h <;> rcases (hpm0 e.2.1 vb hlb) with h' | h' <;> simp [h, h']
        · rw [if_neg (by simp only [beq_iff_eq]; exact hkw)] at hy'; exact hpm0 w' y' hy'
      · intro _ _
        refine ⟨e, List.mem_cons_self, Or.inl (by rw [hla]; rfl), ?_, ?_⟩
        · exact Option.isSome_of_mem (m1 e.1 (e.2.2 * vb) (by rw [hsp1]; exact spinOf_cons_self _ _ _))
        · exact Option.isSome_of_mem (m1 e.2.1 vb (hmp e.2.1 vb hlb))
    · -- some va, none : assign e.2.1
      set sp1 := (e.2.1, e.2.2 * va) :: sp0 with hsp1
      obtain ⟨m1, p1, _⟩ := ih sp1 true sp' ch hsrest hfold
      have hmp : ∀ w y, spinOf sp0 w = some y → spinOf sp1 w = some y :=
        fun w y hy => spinOf_cons_mono _ _ _ hlb hy
      refine ⟨fun w y hy => m1 w y (hmp w y hy), ?_, ?_⟩
      · intro hpm0 w y hy
        refine p1 ?_ w y hy
        intro w' y' hy'
        rw [hsp1, spinOf_cons] at hy'
        by_cases hkw : e.2.1 = w'
        · subst hkw; rw [if_pos (by simp)] at hy'; injection hy' with hy'; subst hy'
          rcases hse with h | h <;> rcases (hpm0 e.1 va hla) with h' | h' <;> simp [h, h']
        · rw [if_neg (by simp only [beq_iff_eq]; exact hkw)] at hy'; exact hpm0 w' y' hy'
      · intro _ _
        refine ⟨e, List.mem_cons_self, Or.inr (by rw [hlb]; rfl), ?_, ?_⟩
        · exact Option.isSome_of_mem (m1 e.1 va (hmp e.1 va hla))
        · exact Option.isSome_of_mem (m1 e.2.1 (e.2.2 * va) (by rw [hsp1]; exact spinOf_cons_self _ _ _))
    · -- some va, some vb : consistency check, no change (or fail)
      by_cases hc : (vb == e.2.2 * va) = true
      · rw [if_pos hc] at hfold
        obtain ⟨m0, p0, w0⟩ := ih sp0 b0 sp' ch hsrest hfold
        refine ⟨m0, p0, ?_⟩
        intro hb0 hch
        obtain ⟨e0, he0, hcnd, hs1, hs2⟩ := w0 hb0 hch
        exact ⟨e0, List.mem_cons_of_mem _ he0, hcnd, hs1, hs2⟩
      · rw [if_neg hc, foldl_stepf_none] at hfold; exact absurd hfold (by simp)

private theorem relaxPass_mono (edges : List SignedEdge) (sp sp' : List (String × Int)) (ch : Bool)
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1)
    (h : relaxPass edges sp = some (sp', ch)) :
    ∀ w y, spinOf sp w = some y → spinOf sp' w = some y := by
  rw [relaxPass_eq] at h; exact (foldMain edges sp false sp' ch hsigns h).1

private theorem relaxPass_pm (edges : List SignedEdge) (sp sp' : List (String × Int)) (ch : Bool)
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1)
    (h : relaxPass edges sp = some (sp', ch)) :
    (∀ w y, spinOf sp w = some y → y = 1 ∨ y = -1) →
      (∀ w y, spinOf sp' w = some y → y = 1 ∨ y = -1) := by
  rw [relaxPass_eq] at h; exact (foldMain edges sp false sp' ch hsigns h).2.1

private theorem relaxPass_witness (edges : List SignedEdge) (sp sp' : List (String × Int))
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1)
    (h : relaxPass edges sp = some (sp', true)) :
    ∃ e0 ∈ edges, ((spinOf sp e0.1).isNone = true ∨ (spinOf sp e0.2.1).isNone = true) ∧
      (spinOf sp' e0.1).isSome = true ∧ (spinOf sp' e0.2.1).isSome = true := by
  rw [relaxPass_eq] at h; exact (foldMain edges sp false sp' true hsigns h).2.2 rfl rfl

/-- A pass that changes nothing (`some (sp, false)`) is a fixed point that certifies balance on every
both-assigned edge. -/
private theorem foldConsistent :
    ∀ (es : List SignedEdge) (sp0 sp : List (String × Int)),
      es.foldl stepf (some (sp0, false)) = some (sp, false) →
      sp0 = sp ∧ ∀ e ∈ es, ∀ va vb, spinOf sp e.1 = some va → spinOf sp e.2.1 = some vb →
        vb = e.2.2 * va := by
  intro es
  induction es with
  | nil =>
    intro sp0 sp h
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1, fun e he => absurd he (by simp)⟩
  | cons e rest ih =>
    intro sp0 sp h
    rw [List.foldl_cons] at h
    rcases hla : spinOf sp0 e.1 with _ | va <;> rcases hlb : spinOf sp0 e.2.1 with _ | vb <;>
      simp only [stepf, hla, hlb] at h
    · obtain ⟨rfl, hcons⟩ := ih sp0 sp h
      refine ⟨rfl, ?_⟩
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he''
      · intro va vb hva _; rw [hla] at hva; exact absurd hva (by simp)
      · exact hcons e' he''
    · exact absurd (foldl_changed_true rest _ sp false h) (by simp)
    · exact absurd (foldl_changed_true rest _ sp false h) (by simp)
    · by_cases hc : (vb == e.2.2 * va) = true
      · rw [if_pos hc] at h
        obtain ⟨rfl, hcons⟩ := ih sp0 sp h
        refine ⟨rfl, ?_⟩
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he''
        · intro va' vb' hva' hvb'
          rw [hla] at hva'; rw [hlb] at hvb'
          injection hva' with hva'; injection hvb' with hvb'; subst hva'; subst hvb'
          rw [beq_iff_eq] at hc; exact hc
        · exact hcons e' he''
      · rw [if_neg hc, foldl_stepf_none] at h; exact absurd h (by simp)

private theorem relaxPass_false_consistent (edges : List SignedEdge) (sp : List (String × Int))
    (h : relaxPass edges sp = some (sp, false)) :
    ∀ e ∈ edges, ∀ va vb, spinOf sp e.1 = some va → spinOf sp e.2.1 = some vb → vb = e.2.2 * va := by
  rw [relaxPass_eq] at h; exact (foldConsistent edges sp sp h).2

private theorem relaxPass_false_eq (edges : List SignedEdge) (sp sp' : List (String × Int))
    (h : relaxPass edges sp = some (sp', false)) : sp' = sp := by
  rw [relaxPass_eq] at h; exact (foldConsistent edges sp sp' h).1.symm

/-- The count of edges with a still-free endpoint: a measure that strictly drops on every productive
pass and is bounded by the edge count, so the fuel `edges.length + 1` always suffices. -/
private def mE (edges : List SignedEdge) (sp : List (String × Int)) : Nat :=
  edges.countP (fun e => (spinOf sp e.1).isNone || (spinOf sp e.2.1).isNone)

private theorem mE_le (edges : List SignedEdge) (sp : List (String × Int)) :
    mE edges sp ≤ edges.length := by unfold mE; exact List.countP_le_length

private theorem mE_decrease (edges : List SignedEdge) (sp sp' : List (String × Int))
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1)
    (h : relaxPass edges sp = some (sp', true)) : mE edges sp' < mE edges sp := by
  have hmono := relaxPass_mono edges sp sp' true hsigns h
  obtain ⟨e0, he0, hcond, hs1, hs2⟩ := relaxPass_witness edges sp sp' hsigns h
  have hnone : ∀ w, (spinOf sp' w).isNone = true → (spinOf sp w).isNone = true := by
    intro w hw
    cases hsw : spinOf sp w with
    | none => rfl
    | some y => rw [hmono w y hsw] at hw; simp at hw
  unfold mE
  refine countP_strict edges _ _ ?_ ?_
  · intro e _ hq
    simp only [Bool.or_eq_true] at hq ⊢
    rcases hq with h1 | h1
    · exact Or.inl (hnone e.1 h1)
    · exact Or.inr (hnone e.2.1 h1)
  · refine ⟨e0, he0, ?_, ?_⟩
    · simp only [Bool.or_eq_true]
      rcases hcond with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · have n1 : (spinOf sp' e0.1).isNone = false := by
        cases hx : spinOf sp' e0.1 with
        | none => rw [hx] at hs1; simp at hs1
        | some => rfl
      have n2 : (spinOf sp' e0.2.1).isNone = false := by
        cases hx : spinOf sp' e0.2.1 with
        | none => rw [hx] at hs2; simp at hs2
        | some => rfl
      rw [n1, n2]; rfl

private theorem relaxToFix_eq (edges : List SignedEdge) (sp : List (String × Int)) :
    relaxToFix edges sp = relaxToFix.loop edges (edges.length + 1) sp := rfl

private theorem loop_zero (edges : List SignedEdge) (sp : List (String × Int)) :
    relaxToFix.loop edges 0 sp = some sp := rfl

private theorem loop_succ (edges : List SignedEdge) (fuel : Nat) (sp : List (String × Int)) :
    relaxToFix.loop edges (fuel + 1) sp =
      match relaxPass edges sp with
      | none => none
      | some (sp', true) => relaxToFix.loop edges fuel sp'
      | some (sp', false) => some sp' := rfl

private theorem loop_succ_none (edges : List SignedEdge) (m : Nat) (sp : List (String × Int))
    (h : relaxPass edges sp = none) : relaxToFix.loop edges (m + 1) sp = none := by rw [loop_succ, h]

private theorem loop_succ_true (edges : List SignedEdge) (m : Nat) (sp sp' : List (String × Int))
    (h : relaxPass edges sp = some (sp', true)) :
    relaxToFix.loop edges (m + 1) sp = relaxToFix.loop edges m sp' := by rw [loop_succ, h]

private theorem loop_succ_false (edges : List SignedEdge) (m : Nat) (sp sp' : List (String × Int))
    (h : relaxPass edges sp = some (sp', false)) :
    relaxToFix.loop edges (m + 1) sp = some sp' := by rw [loop_succ, h]

/-- Fuel sufficiency: with the measure `mE` below the fuel, `relaxToFix.loop` never bottoms out at
fuel `0`; a successful run reaches a genuine fixed point (a `false` pass). -/
private theorem loopFix (edges : List SignedEdge)
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) :
    ∀ (n : Nat) (sp : List (String × Int)), mE edges sp < n →
      relaxToFix.loop edges n sp = none ∨
      ∃ spf, relaxToFix.loop edges n sp = some spf ∧ relaxPass edges spf = some (spf, false) := by
  intro n
  induction n with
  | zero => intro sp hlt; exact absurd hlt (Nat.not_lt_zero _)
  | succ m ih =>
    intro sp hlt
    cases hp : relaxPass edges sp with
    | none => left; exact loop_succ_none edges m sp hp
    | some pr =>
      obtain ⟨sp', ch⟩ := pr
      cases ch with
      | false =>
        right
        refine ⟨sp', loop_succ_false edges m sp sp' hp, ?_⟩
        have heq : sp' = sp := relaxPass_false_eq edges sp sp' hp
        rw [heq]; rw [heq] at hp; exact hp
      | true =>
        have hdec := mE_decrease edges sp sp' hsigns hp
        have hlt' : mE edges sp' < m := by omega
        rw [loop_succ_true edges m sp sp' hp]
        exact ih sp' hlt'

private theorem relaxToFix_fixed (edges : List SignedEdge) (sp spf : List (String × Int))
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1)
    (h : relaxToFix edges sp = some spf) : relaxPass edges spf = some (spf, false) := by
  have hmE : mE edges sp < edges.length + 1 := by have := mE_le edges sp; omega
  have hres := loopFix edges hsigns (edges.length + 1) sp hmE
  rw [relaxToFix_eq] at h
  rcases hres with hnone | ⟨spf', heq, hfix⟩
  · rw [hnone] at h; exact absurd h (by simp)
  · rw [heq] at h; obtain rfl := Option.some.inj h; exact hfix

private theorem loop_mono (edges : List SignedEdge)
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) :
    ∀ (n : Nat) (sp spf : List (String × Int)), relaxToFix.loop edges n sp = some spf →
      ∀ w y, spinOf sp w = some y → spinOf spf w = some y := by
  intro n
  induction n with
  | zero => intro sp spf h; rw [loop_zero] at h; obtain rfl := Option.some.inj h; exact fun w y hy => hy
  | succ m ih =>
    intro sp spf h
    cases hp : relaxPass edges sp with
    | none => rw [loop_succ_none edges m sp hp] at h; exact absurd h (by simp)
    | some pr =>
      obtain ⟨sp', ch⟩ := pr
      cases ch with
      | true =>
        rw [loop_succ_true edges m sp sp' hp] at h
        intro w y hy
        exact ih sp' spf h w y (relaxPass_mono edges sp sp' true hsigns hp w y hy)
      | false =>
        rw [loop_succ_false edges m sp sp' hp] at h
        obtain rfl := Option.some.inj h
        intro w y hy
        exact relaxPass_mono edges sp sp' false hsigns hp w y hy

private theorem loop_pm (edges : List SignedEdge)
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) :
    ∀ (n : Nat) (sp spf : List (String × Int)), relaxToFix.loop edges n sp = some spf →
      (∀ w y, spinOf sp w = some y → y = 1 ∨ y = -1) →
        (∀ w y, spinOf spf w = some y → y = 1 ∨ y = -1) := by
  intro n
  induction n with
  | zero => intro sp spf h; rw [loop_zero] at h; obtain rfl := Option.some.inj h; exact fun hpm => hpm
  | succ m ih =>
    intro sp spf h
    cases hp : relaxPass edges sp with
    | none => rw [loop_succ_none edges m sp hp] at h; exact absurd h (by simp)
    | some pr =>
      obtain ⟨sp', ch⟩ := pr
      cases ch with
      | true =>
        rw [loop_succ_true edges m sp sp' hp] at h
        exact fun hpm => ih sp' spf h (relaxPass_pm edges sp sp' true hsigns hp hpm)
      | false =>
        rw [loop_succ_false edges m sp sp' hp] at h
        obtain rfl := Option.some.inj h
        exact fun hpm => relaxPass_pm edges sp sp' false hsigns hp hpm

private theorem relaxToFix_mono (edges : List SignedEdge) (sp spf : List (String × Int))
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) (h : relaxToFix edges sp = some spf) :
    ∀ w y, spinOf sp w = some y → spinOf spf w = some y := by
  rw [relaxToFix_eq] at h; exact loop_mono edges hsigns _ sp spf h

private theorem relaxToFix_pm (edges : List SignedEdge) (sp spf : List (String × Int))
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) (h : relaxToFix edges sp = some spf) :
    (∀ w y, spinOf sp w = some y → y = 1 ∨ y = -1) →
      (∀ w y, spinOf spf w = some y → y = 1 ∨ y = -1) := by
  rw [relaxToFix_eq] at h; exact loop_pm edges hsigns _ sp spf h

private theorem raw_mem (E : List SignedEdge) (x : String) :
    (x ∈ E.foldr (fun e acc => e.1 :: e.2.1 :: acc) []) ↔ ∃ e ∈ E, x = e.1 ∨ x = e.2.1 := by
  induction E with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldr_cons, List.mem_cons, ih]
    constructor
    · rintro (rfl | rfl | ⟨f, hf, hh⟩)
      · exact ⟨e, by simp, Or.inl rfl⟩
      · exact ⟨e, by simp, Or.inr rfl⟩
      · exact ⟨f, by simp [hf], hh⟩
    · rintro ⟨f, hf, hh⟩
      rcases hf with rfl | hf'
      · rcases hh with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨f, hf', hh⟩)

private theorem dedup_mem (raw : List String) (x : String) :
    (x ∈ raw.foldr (fun y acc => if acc.any (· == y) then acc else y :: acc) []) ↔ x ∈ raw := by
  induction raw with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr_cons, List.mem_cons]
    by_cases hc : (ys.foldr (fun y acc => if acc.any (· == y) then acc else y :: acc) []).any (· == y) = true
    · rw [if_pos hc, ih]
      constructor
      · intro hx; exact Or.inr hx
      · rintro (rfl | hx)
        · rw [List.any_eq_true] at hc
          obtain ⟨z, hz, hzy⟩ := hc
          rw [beq_iff_eq] at hzy; subst hzy; exact ih.mp hz
        · exact hx
    · rw [if_neg hc, List.mem_cons, ih]

private theorem mem_verticesOf_of_edge (edges : List SignedEdge) (e : SignedEdge) (he : e ∈ edges) :
    e.1 ∈ verticesOf edges ∧ e.2.1 ∈ verticesOf edges := by
  have hiff : ∀ x, x ∈ verticesOf edges ↔ ∃ f ∈ edges, x = f.1 ∨ x = f.2.1 := by
    intro x; rw [verticesOf, dedup_mem, raw_mem]
  exact ⟨(hiff e.1).2 ⟨e, he, Or.inl rfl⟩, (hiff e.2.1).2 ⟨e, he, Or.inr rfl⟩⟩

private theorem sign_pm (edges : List SignedEdge) (h : isMonotoneEdges edges = true) :
    ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1 := by
  unfold isMonotoneEdges at h
  split at h
  · exact absurd h (by simp)
  · rename_i hcond
    intro e he
    by_contra hcon
    push_neg at hcon
    refine hcond ?_
    rw [List.any_eq_true]
    refine ⟨e, he, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨by simpa using hcon.1, by simpa using hcon.2⟩

private theorem colorable_true (edges : List SignedEdge) (h : isMonotoneEdges edges = true) :
    colorable edges (verticesOf edges) = true := by
  unfold isMonotoneEdges at h
  split at h
  · exact absurd h (by simp)
  · exact h

/-- Count of still-unassigned vertices: the outer relaxation's fuel measure. -/
private def nfree (edges : List SignedEdge) (sp : List (String × Int)) : Nat :=
  (verticesOf edges).countP (fun v => (spinOf sp v).isNone)

private theorem nfree_mono (edges : List SignedEdge) (spin sp : List (String × Int))
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) (h : relaxToFix edges spin = some sp) :
    nfree edges sp ≤ nfree edges spin := by
  have hmono := relaxToFix_mono edges spin sp hsigns h
  unfold nfree
  apply countP_mono
  intro v _ hv
  cases hx : spinOf spin v with
  | none => rfl
  | some y => have hsv := hmono v y hx; rw [hsv] at hv; simp at hv

private theorem nfree_prepend (edges : List SignedEdge) (sp : List (String × Int)) (v : String)
    (hv : v ∈ verticesOf edges) (hfree : (spinOf sp v).isNone = true) :
    nfree edges ((v, 1) :: sp) < nfree edges sp := by
  unfold nfree
  refine countP_strict _ _ _ ?_ ?_
  · intro u _ hu
    rw [spinOf_cons] at hu
    by_cases hvu : v = u
    · subst hvu; rw [if_pos (by simp)] at hu; simp at hu
    · rw [if_neg (by simp only [beq_iff_eq]; exact hvu)] at hu; exact hu
  · refine ⟨v, hv, hfree, ?_⟩
    show (spinOf ((v, 1) :: sp) v).isNone = false
    rw [spinOf_cons_self]; rfl

private theorem spinFix_go_succ (edges : List SignedEdge) (fuel : Nat) (spin : List (String × Int)) :
    spinFix.go edges (fuel + 1) spin =
      match relaxToFix edges spin with
      | none => spin
      | some sp =>
        match (verticesOf edges).find? (fun v => (spinOf sp v).isNone) with
        | none => sp
        | some v => spinFix.go edges fuel ((v, 1) :: sp) := rfl

private theorem colorable_go_succ (edges : List SignedEdge) (verts : List String) (fuel : Nat)
    (spin : List (String × Int)) :
    colorable.go edges verts (fuel + 1) spin =
      match relaxToFix edges spin with
      | none => false
      | some sp =>
        match verts.find? (fun v => (spinOf sp v).isNone) with
        | none => true
        | some v => colorable.go edges verts fuel ((v, 1) :: sp) := rfl

/-- Under `colorable`, the outer relaxation covers every vertex and lands on a fixed point of `±1`
values: the fuel `|verts|+1` suffices, and success rules out the contradiction branch. -/
private theorem spinFix_go_complete (edges : List SignedEdge)
    (hsigns : ∀ e ∈ edges, e.2.2 = 1 ∨ e.2.2 = -1) :
    ∀ (fuel : Nat) (spin : List (String × Int)),
      (∀ w y, spinOf spin w = some y → y = 1 ∨ y = -1) →
      nfree edges spin < fuel →
      colorable.go edges (verticesOf edges) fuel spin = true →
      (∀ v ∈ verticesOf edges, (spinOf (spinFix.go edges fuel spin) v).isSome = true) ∧
      relaxPass edges (spinFix.go edges fuel spin) = some (spinFix.go edges fuel spin, false) ∧
      (∀ w y, spinOf (spinFix.go edges fuel spin) w = some y → y = 1 ∨ y = -1) := by
  intro fuel
  induction fuel with
  | zero => intro spin _ hlt _; exact absurd hlt (Nat.not_lt_zero _)
  | succ m ih =>
    intro spin hpm hlt hcol
    cases hrf : relaxToFix edges spin with
    | none => simp only [colorable_go_succ, hrf] at hcol; exact absurd hcol (by simp)
    | some sp =>
      have hmono := relaxToFix_mono edges spin sp hsigns hrf
      have hpmsp := relaxToFix_pm edges spin sp hsigns hrf hpm
      cases hfd : (verticesOf edges).find? (fun v => (spinOf sp v).isNone) with
      | none =>
        simp only [spinFix_go_succ, hrf, hfd]
        refine ⟨?_, relaxToFix_fixed edges spin sp hsigns hrf, hpmsp⟩
        intro v hv
        have hn := (List.find?_eq_none.1 hfd) v hv
        cases hsv : spinOf sp v with
        | none => simp [hsv] at hn
        | some y => simp [hsv]
      | some v =>
        have hv_free : (spinOf sp v).isNone = true := by simpa using List.find?_some hfd
        have hv_mem : v ∈ verticesOf edges := List.mem_of_find?_eq_some hfd
        have hpm' : ∀ w y, spinOf ((v, 1) :: sp) w = some y → y = 1 ∨ y = -1 := by
          intro w y hy
          rw [spinOf_cons] at hy
          by_cases hvw : v = w
          · subst hvw; rw [if_pos (by simp)] at hy; injection hy with hy; subst hy; exact Or.inl rfl
          · rw [if_neg (by simp only [beq_iff_eq]; exact hvw)] at hy; exact hpmsp w y hy
        have hle_sp := nfree_mono edges spin sp hsigns hrf
        have hstrict := nfree_prepend edges sp v hv_mem hv_free
        have hlt'' : nfree edges ((v, 1) :: sp) < m := by omega
        simp only [colorable_go_succ, hrf, hfd] at hcol
        simp only [spinFix_go_succ, hrf, hfd]
        exact ih ((v, 1) :: sp) hpm' hlt'' hcol

/-- **Balance.** On a sign-consistent (`isMonotoneEdges`) graph every edge `(j, i, s)` satisfies
`σ i = s · σ j`: the edge's sign is the product of its endpoints' spins. -/
theorem balance (edges : List SignedEdge) (h : isMonotoneEdges edges = true)
    {e : SignedEdge} (he : e ∈ edges) :
    spinAssignment edges e.2.1 = e.2.2 * spinAssignment edges e.1 := by
  have hsigns := sign_pm edges h
  have hcol := colorable_true edges h
  have hcolgo : colorable edges (verticesOf edges)
      = colorable.go edges (verticesOf edges) ((verticesOf edges).length + 1) [] := rfl
  rw [hcolgo] at hcol
  have hpm0 : ∀ w y, spinOf ([] : List (String × Int)) w = some y → y = 1 ∨ y = -1 := by
    intro w y hy; simp [spinOf] at hy
  have hnf0 : nfree edges [] < (verticesOf edges).length + 1 := by
    have hle : nfree edges [] ≤ (verticesOf edges).length := by unfold nfree; exact List.countP_le_length
    omega
  obtain ⟨hcomplete, hfix, hpmfin⟩ :=
    spinFix_go_complete edges hsigns ((verticesOf edges).length + 1) [] hpm0 hnf0 hcol
  have hgo : spinFix edges = spinFix.go edges ((verticesOf edges).length + 1) [] := rfl
  rw [← hgo] at hcomplete hfix hpmfin
  obtain ⟨hv1, hv2⟩ := mem_verticesOf_of_edge edges e he
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.1 (hcomplete e.1 hv1)
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.1 (hcomplete e.2.1 hv2)
  have hcons := relaxPass_false_consistent edges (spinFix edges) hfix e he va vb hva hvb
  have hva1 := hpmfin e.1 va hva
  have hvb1 := hpmfin e.2.1 vb hvb
  have ha : spinAssignment edges e.1 = va := by
    simp only [spinAssignment, hva]; rcases hva1 with h1 | h1 <;> subst h1 <;> decide
  have hb : spinAssignment edges e.2.1 = vb := by
    simp only [spinAssignment, hvb]; rcases hvb1 with h1 | h1 <;> subst h1 <;> decide
  rw [hb, ha]; exact hcons

end GRN
