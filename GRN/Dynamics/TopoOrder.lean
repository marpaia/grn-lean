import Mathlib
import GRN.Dynamics.Interpret
import GRN.Certificate

/-!
# Tier 2 — a topological order for an acyclic GRN

An acyclic regulation relation admits a **topological order**: a rank `order : Species → ℕ` with
`regulates j i → order j < order i`. This is the enumeration the assembled-ODE Jacobian argument
(`GRN.Dynamics.Jacobian`) uses to reindex the state by `Fin n` and read off a (block-)triangular Jacobian.

Acyclicity itself is bridged from a decidable Bool check on the regulation edges (`acyclicBool`): a
concrete `GRN` value discharges `g.Acyclic` by `decide`, feeding the constructive and assembled engines
without a hand-written well-foundedness proof.
-/

namespace GRN

-- UNIT: topo-order
open Classical in
/-- A topological order of the regulated species of an acyclic GRN, as data: a rank in `ℕ` that strictly
increases along every regulation edge. Well-founded recursion on the (acyclic ⟹ well-founded) regulation
relation ranks each species one above the maximum rank of its regulators. -/
noncomputable def topoOrder (g : GRN) (h : g.Acyclic) : g.Species → ℕ :=
  (g.regulates_wf h).fix (fun x ih =>
    Finset.univ.sup (fun k => if hk : g.regulates k x then ih k hk + 1 else 0))

open Classical in
/-- The topological order strictly increases along every regulation edge. -/
theorem topoOrder_lt (g : GRN) (h : g.Acyclic) {j i : g.Species} (hr : g.regulates j i) :
    topoOrder g h j < topoOrder g h i := by
  set f : g.Species → ℕ := fun k => if hk : g.regulates k i then topoOrder g h k + 1 else 0 with hf
  have hunfold : topoOrder g h i = Finset.univ.sup f := (g.regulates_wf h).fix_eq _ i
  have hle : f j ≤ topoOrder g h i := by
    rw [hunfold]; exact Finset.le_sup (Finset.mem_univ j)
  have hfj : f j = topoOrder g h j + 1 := by rw [hf]; exact dif_pos hr
  omega

/-- The regulation edges of a GRN, every input-to-output pair carried with a placeholder `+1` sign — the
directed graph on which `acyclicBool` searches for cycles (unlike `signedInteractionGraph`, it keeps every
regulation edge, including non-monotone ones). -/
def regEdges (g : GRN) : List SignedEdge :=
  g.operators.foldr (fun op acc =>
    (g.inputsOf op.id).foldr (fun src acc2 =>
      (g.outputsOf op.id).map (fun dst => (src, dst, (1 : Int))) ++ acc2) acc) []

/-- A decidable acyclicity check: the regulation graph has no directed cycle. -/
def acyclicBool (g : GRN) : Bool := (cycleSignsEdges (regEdges g)).isEmpty

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

-- dedup foldr preserves membership
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

private theorem verticesOf_mem (E : List SignedEdge) (x : String) :
    x ∈ verticesOf E ↔ ∃ e ∈ E, x = e.1 ∨ x = e.2.1 := by
  rw [verticesOf]
  rw [dedup_mem, raw_mem]

-- neighbor membership from an edge
private theorem mem_neighbors (E : List SignedEdge) (u b : String) (s : Int) (h : (u, b, s) ∈ E) :
    (b, s) ∈ neighbors E u := by
  simp only [neighbors, List.mem_filterMap]
  exact ⟨(u, b, s), h, by simp⟩

private theorem mem_foldr_init {β α : Type*} (l : List β) (X : β → List α) (init : List α) (y : α)
    (hy : y ∈ init) : y ∈ l.foldr (fun x acc => X x ++ acc) init := by
  induction l with
  | nil => simpa using hy
  | cons x xs ih => simp only [List.foldr_cons, List.mem_append]; exact Or.inr ih

private theorem mem_foldr_of_mem {β α : Type*} (l : List β) (X : β → List α) (init : List α) (y : α)
    (x : β) (hx : x ∈ l) (hy : y ∈ X x) : y ∈ l.foldr (fun z acc => X z ++ acc) init := by
  induction l with
  | nil => simp at hx
  | cons z zs ih =>
    simp only [List.foldr_cons, List.mem_append]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Or.inl hy
    · exact Or.inr (ih hx')

-- edge from regulates
private theorem edge_of_regulates (g : GRN) (a b : g.Species) (h : g.regulates a b) :
    ((a : String), (b : String), (1 : Int)) ∈ regEdges g := by
  obtain ⟨op, hop, hin, hout⟩ := h
  rw [regEdges]
  suffices H : ∀ ops : List Node, op ∈ ops →
      ((a : String), (b : String), (1 : Int)) ∈ ops.foldr (fun op acc =>
        (g.inputsOf op.id).foldr (fun src acc2 =>
          (g.outputsOf op.id).map (fun dst => (src, dst, (1 : Int))) ++ acc2) acc) [] by
    exact H g.operators hop
  intro ops hop'
  induction ops with
  | nil => simp at hop'
  | cons o os ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hop' with rfl | hop''
    · exact mem_foldr_of_mem _ _ _ _ (a : String) hin
        (by simp only [List.mem_map]; exact ⟨(b : String), hout, rfl⟩)
    · exact mem_foldr_init _ _ _ _ (ih hop'')

-- nonemptiness propagation through the DFS body fold
private theorem foldr_dfs_ne (E : List SignedEdge) (fuel : ℕ) (start : String) (path : List String)
    (prod : Int) (ns : List (String × Int))
    (hw : ∃ nb ∈ ns, nb.1 = start ∨
          (¬ (path.any (· == nb.1)) ∧
           cycleSignsEdges.dfs E fuel start nb.1 (nb.1 :: path) (prod * nb.2) ≠ [])) :
    ns.foldr (fun nb acc =>
      if nb.1 == start then (prod * nb.2) :: acc
      else if path.any (· == nb.1) then acc
      else cycleSignsEdges.dfs E fuel start nb.1 (nb.1 :: path) (prod * nb.2) ++ acc) [] ≠ [] := by
  induction ns with
  | nil => simp at hw
  | cons nb0 rest ih =>
    simp only [List.foldr_cons]
    -- name the accumulator
    set acc := rest.foldr (fun nb acc =>
      if nb.1 == start then (prod * nb.2) :: acc
      else if path.any (· == nb.1) then acc
      else cycleSignsEdges.dfs E fuel start nb.1 (nb.1 :: path) (prod * nb.2) ++ acc) [] with hacc
    obtain ⟨nb, hnb, hW⟩ := hw
    rcases List.mem_cons.mp hnb with rfl | hrest
    · -- witness is nb0
      rcases hW with hstart | ⟨hnp, hdfs⟩
      · have : (nb.1 == start) = true := by rw [beq_iff_eq]; exact hstart
        rw [if_pos this]; simp
      · by_cases hs : (nb.1 == start) = true
        · rw [if_pos hs]; simp
        · rw [if_neg hs, if_neg hnp]
          intro hc
          rw [List.append_eq_nil_iff] at hc
          exact hdfs hc.1
    · -- witness in rest: acc ≠ []
      have hacc_ne : acc ≠ [] := ih ⟨nb, hrest, hW⟩
      by_cases hs : (nb0.1 == start) = true
      · rw [if_pos hs]; simp
      · rw [if_neg hs]
        by_cases hp : path.any (· == nb0.1) = true
        · rw [if_pos hp]; exact hacc_ne
        · rw [if_neg hp]
          intro hc
          rw [List.append_eq_nil_iff] at hc
          exact hacc_ne hc.2

private theorem dfs_complete (E : List SignedEdge) (start : String) :
    ∀ (l : List String) (fuel : ℕ) (node : String) (path : List String) (prod : Int),
    List.IsChain (fun a b => ∃ s, (a, b, s) ∈ E) (node :: l) →
    l ≠ [] → l.getLast? = some start →
    l.dropLast.Nodup → (∀ x ∈ l.dropLast, x ∉ path) → start ∈ path →
    l.length ≤ fuel →
    cycleSignsEdges.dfs E fuel start node path prod ≠ [] := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
  | cons w1 rest ih =>
    intro fuel node path prod hchain _ hlast hnodup hpath hstart hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := by
      cases fuel with
      | zero => simp at hfuel
      | succ f => exact ⟨f, rfl⟩
    -- edge node → w1
    have hrel : ∃ s, (node, w1, s) ∈ E := hchain.rel_head
    obtain ⟨s, hs⟩ := hrel
    have hnb : (w1, s) ∈ neighbors E node := mem_neighbors E node w1 s hs
    simp only [cycleSignsEdges.dfs]
    refine foldr_dfs_ne E f start path prod (neighbors E node) ?_
    refine ⟨(w1, s), hnb, ?_⟩
    by_cases hrest : rest = []
    · -- base: w1 = start
      subst hrest
      left
      simpa using hlast
    · -- recurse
      right
      constructor
      · -- w1 ∉ path
        have hw1mem : w1 ∈ (w1 :: rest).dropLast := by
          rw [List.dropLast_cons_of_ne_nil hrest]; exact List.mem_cons_self
        have hwp := hpath w1 hw1mem
        simp only [List.any_eq_true, not_exists, not_and]
        intro x hx hc
        rw [beq_iff_eq] at hc
        subst hc
        exact hwp hx
      · -- dfs from w1 nonempty by IH
        apply ih f w1 (w1 :: path) (prod * s)
        · exact hchain.tail
        · exact hrest
        · have hg : (w1 :: rest).getLast? = rest.getLast? := by
            cases rest with
            | nil => exact absurd rfl hrest
            | cons _ _ => rfl
          rw [← hg]; exact hlast
        · have : (w1 :: rest).dropLast.Nodup := hnodup
          rw [List.dropLast_cons_of_ne_nil hrest] at this
          exact this.of_cons
        · intro x hx
          have hxd : x ∈ (w1 :: rest).dropLast := by
            rw [List.dropLast_cons_of_ne_nil hrest]; exact List.mem_cons_of_mem _ hx
          have hxp : x ∉ path := hpath x hxd
          have hnd : (w1 :: rest).dropLast.Nodup := hnodup
          rw [List.dropLast_cons_of_ne_nil hrest] at hnd
          simp only [List.mem_cons, not_or]
          refine ⟨?_, hxp⟩
          rintro rfl
          exact (List.nodup_cons.mp hnd).1 hx
        · exact List.mem_cons_of_mem _ hstart
        · simp only [List.length_cons] at hfuel ⊢; omega

private theorem simpleClosedWalk {α : Type*} (R : α → α → Prop) (v : α) :
    ∀ (n : ℕ) (p : List α), p.length ≤ n → List.IsChain R p →
      p.head? = some v → p.getLast? = some v → 2 ≤ p.length →
      ∃ q, List.IsChain R q ∧ q.head? = some v ∧ q.getLast? = some v ∧
        2 ≤ q.length ∧ q.dropLast.Nodup := by
  intro n
  induction n with
  | zero => intro p hle _ _ _ h2; omega
  | succ n ih =>
    intro p hle hchain hhead hlast h2
    by_cases hnd : p.dropLast.Nodup
    · exact ⟨p, hchain, hhead, hlast, h2, hnd⟩
    · -- find duplicate indices in dropLast
      rw [List.nodup_iff_getElem?_ne_getElem?] at hnd
      push_neg at hnd
      obtain ⟨i, j, hij, hjlen, heq⟩ := hnd
      -- dropLast index → p index
      have hdl : p.dropLast.length = p.length - 1 := List.length_dropLast
      have hjp : j < p.length := by omega
      have hip : i < p.length := by omega
      have hj1p : j + 1 < p.length := by omega
      have hpi : p.dropLast[i]? = p[i]? := by
        rw [List.dropLast_eq_take, List.getElem?_take_of_lt (by omega)]
      have hpj : p.dropLast[j]? = p[j]? := by
        rw [List.dropLast_eq_take, List.getElem?_take_of_lt (by omega)]
      rw [hpi, hpj] at heq
      rw [List.getElem?_eq_getElem hip, List.getElem?_eq_getElem hjp, Option.some_inj] at heq
      -- the two segments
      set A := p.take (i + 1) with hA
      set B := p.drop (j + 1) with hB
      have hAlen : A.length = i + 1 := by rw [hA, List.length_take]; omega
      have hBlen : B.length = p.length - (j + 1) := by rw [hB, List.length_drop]
      have hAne : A ≠ [] := by rw [← List.length_pos_iff]; omega
      have hBne : B ≠ [] := by rw [← List.length_pos_iff]; omega
      refine ih (A ++ B) ?_ ?_ ?_ ?_ ?_
      · rw [List.length_append, hAlen, hBlen]; omega
      · -- IsChain (A ++ B)
        refine (hchain.take (i + 1)).append (hchain.drop (j + 1)) ?_
        intro x hx y hy
        -- x = p[i], y = p[j+1]
        have hxi : x = p[i] := by
          have hget : A.getLast? = p[i]? := by
            rw [List.getLast?_eq_getElem?, hA, List.length_take,
              show min (i + 1) p.length - 1 = i by omega, List.getElem?_take_of_lt (by omega)]
          rw [hget, List.getElem?_eq_getElem hip, Option.mem_def, Option.some_inj] at hx
          exact hx.symm
        have hyj : y = p[j + 1] := by
          have hget : B.head? = p[j + 1]? := by
            rw [List.head?_eq_getElem?, hB, List.getElem?_drop]
          rw [hget, List.getElem?_eq_getElem hj1p, Option.mem_def, Option.some_inj] at hy
          exact hy.symm
        have hstep : R p[j] p[j + 1] := by
          rw [List.isChain_iff_getElem] at hchain
          exact hchain j hj1p
        rw [hxi, hyj, heq]; exact hstep
      · -- head? (A ++ B) = some v
        rw [List.head?_append_of_ne_nil A hAne, List.head?_eq_getElem?, hA,
          List.getElem?_take_of_lt (by omega)]
        rw [List.head?_eq_getElem?] at hhead; exact hhead
      · -- getLast? (A ++ B) = some v
        rw [List.getLast?_append_of_ne_nil A hBne, List.getLast?_eq_getElem?, hBlen, hB,
          List.getElem?_drop]
        rw [List.getLast?_eq_getElem?] at hlast
        rw [show j + 1 + (p.length - (j + 1) - 1) = p.length - 1 by omega]
        exact hlast
      · rw [List.length_append, hAlen, hBlen]; omega

private theorem foldr_append_ne {α β : Type*} (L : List α) (F : α → List β) (v : α)
    (hv : v ∈ L) (hF : F v ≠ []) :
    L.foldr (fun v acc => F v ++ acc) [] ≠ [] := by
  induction L with
  | nil => simp at hv
  | cons a rest ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hv with rfl | hv'
    · intro hc; rw [List.append_eq_nil_iff] at hc; exact hF hc.1
    · intro hc; rw [List.append_eq_nil_iff] at hc; exact ih hv' hc.2

-- UNIT: acyclic-decide
/-- **Bool acyclicity ⟹ `Acyclic`.** If the Bool cycle check on the regulation edges passes, no species
transitively regulates itself, so a concrete `GRN` value discharges `g.Acyclic` by `decide`. -/
theorem acyclic_of_acyclicBool (g : GRN) (h : g.acyclicBool = true) : g.Acyclic := by
  rw [acyclicBool, List.isEmpty_iff] at h
  intro i htg
  set E := regEdges g with hE
  set v : String := (i : String) with hv
  -- lift to string-edge TransGen
  have hlift : Relation.TransGen (fun a b => ∃ s, (a, b, s) ∈ E) v v := by
    refine Relation.TransGen.lift (Subtype.val) ?_ htg
    intro a b hr
    exact ⟨1, edge_of_regulates g a b hr⟩
  obtain ⟨c, hac, hcv⟩ := Relation.TransGen.head'_iff.mp hlift
  obtain ⟨L, hLchain, hLlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hcv
  -- full closed walk p = v :: c :: L
  set p : List String := v :: c :: L with hp
  have hpchain : List.IsChain (fun a b => ∃ s, (a, b, s) ∈ E) p := by
    rw [hp, List.isChain_cons]
    exact ⟨fun y hy => by simp only [List.head?_cons, Option.mem_some_iff] at hy; exact hy ▸ hac,
      hLchain⟩
  have hphead : p.head? = some v := by rw [hp]; rfl
  have hplast : p.getLast? = some v := by
    rw [hp, List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _), hLlast]
  have hp2 : 2 ≤ p.length := by rw [hp]; simp
  obtain ⟨q, hqchain, hqhead, hqlast, hq2, hqnodup⟩ :=
    simpleClosedWalk (fun a b => ∃ s, (a, b, s) ∈ E) v p.length p le_rfl hpchain hphead hplast hp2
  -- all vertices of q are graph vertices
  have hvert : ∀ x ∈ q, x ∈ verticesOf E := by
    have hqc := hqchain
    rw [List.isChain_iff_getElem] at hqc
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    by_cases hnext : k + 1 < q.length
    · obtain ⟨s, hs⟩ := hqc k hnext
      exact (verticesOf_mem E q[k]).mpr ⟨(q[k], q[k+1], s), hs, Or.inl rfl⟩
    · have hkm : (k - 1) + 1 < q.length := by omega
      obtain ⟨s, hs⟩ := hqc (k - 1) hkm
      have heqk : q[(k-1)+1] = q[k] := by congr 1; omega
      rw [heqk] at hs
      exact (verticesOf_mem E q[k]).mpr ⟨(q[k-1], q[k], s), hs, Or.inr rfl⟩
  -- cons form of q
  obtain ⟨l, rfl⟩ : ∃ l, q = v :: l :=
    ⟨q.tail, List.eq_cons_of_mem_head? (Option.mem_def.mpr hqhead)⟩
  have hlne : l ≠ [] := by
    intro hnil; rw [hnil] at hq2; simp at hq2
  have hdropcons : (v :: l).dropLast = v :: l.dropLast := List.dropLast_cons_of_ne_nil hlne
  rw [hdropcons] at hqnodup
  obtain ⟨hvnotin, hlnodup⟩ := List.nodup_cons.mp hqnodup
  have hllast : l.getLast? = some v := by
    have : (v :: l).getLast? = l.getLast? := by
      cases l with
      | nil => exact absurd rfl hlne
      | cons _ _ => rfl
    rw [← this]; exact hqlast
  -- dfs from v is nonempty
  have hdfs : cycleSignsEdges.dfs E ((verticesOf E).length + 1) v v [v] 1 ≠ [] := by
    apply dfs_complete E v l ((verticesOf E).length + 1) v [v] 1 hqchain hlne hllast hlnodup
    · intro x hx
      simp only [List.mem_singleton]
      rintro rfl
      exact hvnotin hx
    · exact List.mem_singleton.mpr rfl
    · -- l.length ≤ verts.length + 1
      have hsub : (v :: l).dropLast ⊆ verticesOf E :=
        fun x hx => hvert x (List.dropLast_subset _ hx)
      have hnd : (v :: l).dropLast.Nodup := by rw [hdropcons]; exact hqnodup
      have hle := (List.subperm_of_subset hnd hsub).length_le
      rw [hdropcons] at hle
      have hdl : l.dropLast.length = l.length - 1 := List.length_dropLast
      have hlpos : 1 ≤ l.length := List.length_pos_iff.mpr hlne
      simp only [List.length_cons] at hle ⊢
      omega
  -- outer fold nonempty
  have hne : cycleSignsEdges E ≠ [] := by
    rw [cycleSignsEdges]
    exact foldr_append_ne (verticesOf E)
      (fun w => cycleSignsEdges.dfs E ((verticesOf E).length + 1) w w [w] 1) v
      (hvert v List.mem_cons_self) hdfs
  exact hne h

end GRN
