import Mathlib
import GRN.Dynamics.Jacobian

/-!
# Tier 2 — unifying the constructive and assembled engines

Two independent proofs deliver the unique steady state of an acyclic GRN: the constructive
forward-substitution `steadyPoint` of the feedforward IR (`GRN.Dynamics.Feedforward`), and the
assembled-ODE equilibrium obtained through Gale–Nikaido univalence (`GRN.Dynamics.Jacobian`). This module
identifies them: any equilibrium of the assembled field, reindexed by an enumeration `e`, equals the
constructive `steadyPoint`. Both are THE unique steady state, merging the two engines.
-/

namespace GRN

open Dynamics

-- UNIT: steadyPoint-eq-equilibrium
/-- **The assembled equilibrium is the constructive steady point.** For an acyclic, well-posed GRN, any
zero of the assembled field (reindexed by `e : Fin n ≃ Species`) coincides with the constructive
forward-substitution `steadyPoint` — the two steady-state engines agree. -/
theorem steadyPoint_eq_equilibrium (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed)
    {n : ℕ} (e : Fin n ≃ g.Species) (x : Fin n → ℝ)
    (hx : Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) x = 0) :
    x = fun k => (g.toSystem hac wp).steadyPoint (e k) := by sorry

end GRN
