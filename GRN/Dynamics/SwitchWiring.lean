import Mathlib
import GRN.Dynamics.Jacobian
import GRN.Certificate

/-!
# Tier 2 — switch wiring (Thomas / Soulé)

The switch certificate is Thomas' rule: a positive feedback cycle is *necessary* for multistationarity.
The dynamical content is on the assembled Jacobian: if the signed interaction graph carries no positive
feedback cycle, every cycle-cover term of the negated-field Jacobian `negJac` shares the diagonal term's
sign — the sign-definite hypothesis of `jacobian_nonsingular_of_signDefinite`.

Assembling those cover-term signs makes the Jacobian nonsingular, so the equilibrium is locally isolated.
Hence multistationarity (a bistable, two-state switch) requires a positive feedback cycle.
-/

namespace GRN

open Dynamics CRNT
open scoped Matrix

-- UNIT: coverterm-of-nocycle
/-- **No positive cycle ⟹ sign-definite cover terms.** If the signed interaction graph has no positive
feedback loop, every cycle-cover term of the negated-field Jacobian `negJac` is nonnegative and the
diagonal term is strictly positive — the sign-definite hypothesis feeding
`jacobian_nonsingular_of_signDefinite`. -/
theorem coverTerm_signDefinite_of_noPositiveLoop (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) (hz : ∀ k, 0 < z k)
    (hnopos : hasPositiveLoopEdges (signedInteractionGraph g) = false) :
    (∀ σ : Equiv.Perm (Fin n), 0 ≤ coverTerm (g.negJac wp e E) σ) ∧
      0 < coverTerm (g.negJac wp e E) 1 := by sorry

-- UNIT: grn-switch-isolation
/-- **Local isolation of the equilibrium.** Assembling the cover-term signs and applying
`jacobian_nonsingular_of_signDefinite`: with no positive feedback cycle the assembled Jacobian is
nonsingular, so the equilibrium is locally isolated — multistationarity requires a positive cycle
(Thomas / Soulé). -/
theorem grn_switch_isolation (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) (hz : ∀ k, 0 < z k)
    (hnopos : hasPositiveLoopEdges (signedInteractionGraph g) = false) :
    (g.negJac wp e E).det ≠ 0 := by sorry

end GRN
