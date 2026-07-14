import Mathlib
import GRN.Dynamics.Jacobian
import GRN.Certificate
import CRNT.Multistationarity.JacobianDeterminantSign

/-!
# Tier 2 — analytic entry signs and the Thomas / Soulé combinatorial core

The full close of the switch frontier connects three layers, so that the assembled Jacobian's
cover terms are sign-definite exactly when the signed interaction graph carries no positive
feedback cycle:

* **Concrete signed derivatives.** The pointwise derivative sign of an interpreted rate with
  respect to one regulator input at a strictly positive state: `hill` is globally monotone, so its
  sign is `pairSign`; `hill2` matches `signFromPairs` on monotone ports; a `sum` summand reuses the
  `hill` sign.
* **Entry-sign assembly.** From the per-operator derivative signs, the production Jacobian's
  off-diagonal entry `(r, c)` weakly matches the interaction-graph edge sign from `e c` to `e r`, so
  the negated-field Jacobian `negJac` carries the *opposite* sign off the diagonal and, with no
  positive self-loop, a strictly positive diagonal.
* **Combinatorial Thomas / Soulé.** A `Perm`-cycle of `Fin n` corresponds to a directed cycle
  enumerated by `cycleSignsEdges`; a matrix with a positive diagonal whose single-cycle cover terms
  are all nonnegative has every cover term nonnegative and a strictly positive diagonal term.

The scope excludes non-monotone (`sign = 0`) interaction edges: a non-monotone `hill2` port has graph
sign `0` yet a definite nonzero pointwise derivative that could close a positive cycle. The hypothesis
`hmono` (every edge carries `±1`) rules those out.
-/

namespace GRN

open Dynamics CRNT
open scoped Matrix

/-! ## Interaction-graph edge sign lookup

`graphEdgeSign g src dst` reads the sign of the edge `src → dst` in the signed interaction graph
(`0` when absent). It is the integer sign the analytic derivative of the interpreted rate is matched
against. -/

/-- The sign of the interaction-graph edge from `src` to `dst` (`0` if there is no such edge). -/
def graphEdgeSign (g : GRN) (src dst : String) : Int :=
  match (g.signedInteractionGraph).find? (fun e => e.1 == src && e.2.1 == dst) with
  | some e => e.2.2
  | none => 0

/-! ## Layer 1 — concrete signed derivatives of the interpreted rates

Each lemma exposes the pointwise derivative and pins its sign at a strictly positive input. -/

-- UNIT: hill-deriv-sign  (analytic; globally monotone, tractable)
/-- **Single-input Hill derivative sign.** At a strictly positive input the derivative of the Hill
response exists and its sign is `pairSign a0 a1`: positive when `a0 < a1` (activation), negative when
`a1 < a0` (repression), zero when `a0 = a1`. Globally monotone, so the sign is context-free. -/
theorem hill_hasDerivAt_sign (a0 a1 K n u : ℝ) (hK : 0 < K) (hn : 0 < n) (hu : 0 < u) :
    ∃ d : ℝ, HasDerivAt (fun t => hill a0 a1 K n t) d u ∧
      (a0 < a1 → 0 < d) ∧ (a1 < a0 → d < 0) ∧ (a0 = a1 → d = 0) := by
  sorry

-- UNIT: hill2-deriv-left  (analytic; HARD — wall risk)
/-- **Two-input Hill left-port derivative sign.** At a strictly positive pair the derivative of the
`hill2` response in its first input exists and, on a monotone left port, matches
`signFromPairs [(a0,a1),(a2,a3)]`.

This is the hard, wall-risk piece. The sign of `∂/∂u₁` is `sign ((a1 − a0) + (a3 − a2)·r₂)` with
`r₂ = (u₂/K₂)^{n₂} > 0`; a monotone left port makes both coefficients same-signed and one strict, so
strict positivity of the co-input `u₂` is required for the strict conclusion (a non-monotone port —
excluded by `hmono` — would give a mixed sign). -/
theorem hill2_hasDerivAt_left_sign (a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 : ℝ)
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 < n1) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    ∃ d : ℝ, HasDerivAt (fun t => hill2 a0 a1 a2 a3 K1 K2 n1 n2 t u2) d u1 ∧
      ((a0 ≤ a1 ∧ a2 ≤ a3 ∧ (a0 < a1 ∨ a2 < a3)) → 0 < d) ∧
      ((a1 ≤ a0 ∧ a3 ≤ a2 ∧ (a1 < a0 ∨ a3 < a2)) → d < 0) := by
  sorry

-- UNIT: hill2-deriv-right  (analytic; HARD — wall risk)
/-- **Two-input Hill right-port derivative sign.** The right-port companion of
`hill2_hasDerivAt_left_sign`: at a strictly positive pair the derivative in the second input matches
`signFromPairs [(a0,a2),(a1,a3)]` on a monotone right port. The sign of `∂/∂u₂` is
`sign ((a2 − a0) + (a3 − a1)·r₁)`. -/
theorem hill2_hasDerivAt_right_sign (a0 a1 a2 a3 K1 K2 n1 n2 u1 u2 : ℝ)
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn2 : 0 < n2) (hu1 : 0 < u1) (hu2 : 0 < u2) :
    ∃ d : ℝ, HasDerivAt (fun t => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 t) d u2 ∧
      ((a0 ≤ a2 ∧ a1 ≤ a3 ∧ (a0 < a2 ∨ a1 < a3)) → 0 < d) ∧
      ((a2 ≤ a0 ∧ a3 ≤ a1 ∧ (a2 < a0 ∨ a3 < a1)) → d < 0) := by
  sorry

-- UNIT: sum-deriv-sign  (analytic; per-input summand reuses `hill`)
/-- **`sum`-operator per-input derivative sign.** A `sum` summand is a single-input Hill in one input
only, so the port derivative reuses the `hill` sign: nonnegative on an activating summand
(`a0 ≤ a1`), matching the `+1` sign `operatorInputSigns` assigns every `sum` port. -/
theorem sum_summand_hasDerivAt_nonneg (a0 a1 K n u : ℝ)
    (hK : 0 < K) (hn : 0 < n) (hu : 0 < u) (ha : a0 ≤ a1) :
    ∃ d : ℝ, HasDerivAt (fun t => hill a0 a1 K n t) d u ∧ 0 ≤ d := by
  sorry

/-! ## Layer 2 — concrete directional derivative and entry-sign assembly

`assembledProd_hasDerivAt_dir` strengthens `hasFDerivAt_assembledProd` by naming the concrete
`c`-directional derivative of the `r`-coordinate, which the abstract `fderiv` hides. The entry-sign
lemmas read the interaction-graph edge sign off that derivative. -/

-- UNIT: assembledprod-dir-deriv  (analytic/structural; strengthens `hasFDerivAt_assembledProd`)
/-- **Concrete directional derivative of the assembled production.** At a strictly positive state the
`c`-axis derivative of the `r`-coordinate of `assembledProd` exists as a named scalar `d`, and every
Fréchet derivative `E` reads it as the Jacobian entry `jacobianMatrix E r c`. This exposes the
closed-form entry that `hasFDerivAt_assembledProd` leaves as an opaque `fderiv`, so entry signs can be
read from the Layer-1 rate derivatives. -/
theorem assembledProd_hasDerivAt_dir (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (z : Fin n → ℝ) (hz : ∀ k, 0 < z k) (r c : Fin n) :
    ∃ d : ℝ, HasDerivAt (fun t : ℝ => g.assembledProd wp e (z + t • Pi.single c (1 : ℝ)) r) d 0 ∧
      ∀ E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
        HasFDerivAt (g.assembledProd wp e) E z → jacobianMatrix E r c = d := by
  sorry

-- UNIT: negjac-sign-matches  (assembly; the internal `NegJacSignMatches` content)
/-- **`negJac` off-diagonal signs match the negated interaction-graph edge signs.** For `r ≠ c`, at a
strictly positive state and under `hmono`, the entry `negJac r c` carries the sign *opposite* to the
graph edge from `e c` to `e r`: an activating edge (`+1`) gives a nonpositive entry, a repressing edge
(`−1`) a nonnegative entry, and an absent edge (`0`) a zero entry. Weak inequalities absorb the
degenerate case where an activating co-input Hill contributes a vanishing derivative. -/
theorem negJac_offDiag_signMatches (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) (hz : ∀ k, 0 < z k)
    (hmono : ∀ edge ∈ signedInteractionGraph g, edge.2.2 = 1 ∨ edge.2.2 = -1)
    (r c : Fin n) (hrc : r ≠ c) :
    (0 < graphEdgeSign g (e c) (e r) → g.negJac wp e E r c ≤ 0) ∧
      (graphEdgeSign g (e c) (e r) < 0 → 0 ≤ g.negJac wp e E r c) ∧
      (graphEdgeSign g (e c) (e r) = 0 → g.negJac wp e E r c = 0) := by
  sorry

-- UNIT: negjac-diag-pos  (assembly)
/-- **`negJac` has a strictly positive diagonal under no positive loop.** The diagonal entry is the
positive degradation rate minus the self-regulation derivative. With no positive feedback loop, no
species carries a positive self-loop (a length-one positive cycle), so every self-regulation
contribution is nonpositive and degradation dominates. -/
theorem negJac_diag_pos (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) (hz : ∀ k, 0 < z k)
    (hmono : ∀ edge ∈ signedInteractionGraph g, edge.2.2 = 1 ∨ edge.2.2 = -1)
    (hnopos : hasPositiveLoopEdges (signedInteractionGraph g) = false) :
    ∀ k, 0 < g.negJac wp e E k k := by
  sorry

/-! ## Layer 3 — the combinatorial Thomas / Soulé core

Matrix-level and reusable: no positive cycle in a sign pattern with a positive diagonal forces
sign-definite cover terms. The `Perm`-cycle ↔ directed-graph-cycle correspondence is the genuinely
new sub-lemma linking `Equiv.Perm (Fin n)` cycles to the cycles `cycleSignsEdges` enumerates. -/

-- UNIT: cyclesigns-nonpos  (combinatorial; unfolds `hasPositiveLoopEdges`)
/-- **No positive loop bounds every enumerated cycle sign.** When `hasPositiveLoopEdges` is `false`,
every sign product `cycleSignsEdges` enumerates is nonpositive. -/
theorem cycleSignsEdges_nonpos_of_noPositiveLoop (edges : List SignedEdge)
    (h : hasPositiveLoopEdges edges = false) :
    ∀ s ∈ cycleSignsEdges edges, s ≤ 0 := by
  sorry

-- UNIT: perm-cycle-correspondence  (combinatorial; the new sub-lemma)
/-- **A `Perm`-cycle is a directed graph cycle.** A nontrivial cycle `σ` of `Fin n` whose every step
`e i → e (σ i)` is a real regulation edge maps to a directed cycle enumerated by `cycleSignsEdges`:
the product of the graph edge signs around `σ`'s orbit occurs in
`cycleSignsEdges (signedInteractionGraph g)`. This is the bridge between the algebraic cover-term
index (`Equiv.Perm`) and the graph-combinatorial cycle enumeration. -/
theorem cycleSign_mem_cycleSignsEdges (g : GRN) {n : ℕ} (e : Fin n ≃ g.Species)
    (σ : Equiv.Perm (Fin n)) (hσ : σ.IsCycle)
    (hstep : ∀ i ∈ σ.support, g.regulates (e i) (e (σ i))) :
    (∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i))) ∈
      cycleSignsEdges (signedInteractionGraph g) := by
  sorry

-- UNIT: coverterm-of-cycles  (combinatorial CORE; matrix-level, reusable)
/-- **Sign-definite cover terms from single-cycle signs.** A matrix with a strictly positive diagonal
whose every *cyclic* permutation has a nonnegative cover term has every cover term nonnegative and a
strictly positive diagonal (identity) term. Factoring a permutation's cover term over its disjoint
cycles (`cycleFactorsFinset`) reduces sign-definiteness to the single-cycle condition; the fixed
points contribute the positive diagonal factors. -/
theorem coverTerm_signDefinite_of_cycles {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hdiag : ∀ i, 0 < M i i)
    (hcyc : ∀ σ : Equiv.Perm (Fin n), σ.IsCycle → 0 ≤ coverTerm M σ) :
    (∀ σ : Equiv.Perm (Fin n), 0 ≤ coverTerm M σ) ∧ 0 < coverTerm M 1 := by
  sorry

-- UNIT: negjac-cycle-nonneg  (assembly; bridges Layer 2 and Layer 3)
/-- **Single-cycle cover terms of `negJac` are nonnegative under no positive loop.** For a cyclic
permutation `σ`, the cover term `coverTerm negJac σ` factors as `coverCoeff σ` times the product of
`negJac` entries around the orbit. Each off-diagonal factor's sign is the negated graph edge sign
(`negJac_offDiag_signMatches`), the orbit is a directed graph cycle
(`cycleSign_mem_cycleSignsEdges`), and its graph sign product is nonpositive
(`cycleSignsEdges_nonpos_of_noPositiveLoop`); the length parity in `coverCoeff` cancels the
sign flips from `negJac = γ − E`, leaving a nonnegative term. -/
theorem negJac_coverTerm_cycle_nonneg (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) (hz : ∀ k, 0 < z k)
    (hmono : ∀ edge ∈ signedInteractionGraph g, edge.2.2 = 1 ∨ edge.2.2 = -1)
    (hnopos : hasPositiveLoopEdges (signedInteractionGraph g) = false)
    (σ : Equiv.Perm (Fin n)) (hσ : σ.IsCycle) :
    0 ≤ coverTerm (g.negJac wp e E) σ := by
  sorry

end GRN
