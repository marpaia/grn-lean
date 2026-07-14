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

/-- **The assembled equilibrium is the constructive steady point.** For an acyclic, well-posed GRN, any
zero of the assembled field (reindexed by `e : Fin n ≃ Species`) coincides with the constructive
forward-substitution `steadyPoint` — the two steady-state engines agree. -/
theorem steadyPoint_eq_equilibrium (g : GRN) (hac : g.Acyclic) (wp : g.WellPosed)
    {n : ℕ} (e : Fin n ≃ g.Species) (x : Fin n → ℝ)
    (hx : Dynamics.field (fun k => wp.γ (e k)) (g.assembledProd wp e) x = 0) :
    x = fun k => (g.toSystem hac wp).steadyPoint (e k) := by
  -- Reindex `x` back to a species-valued state and show it is a steady state of the
  -- constructive feedforward system. Uniqueness of that steady state then pins it to `steadyPoint`.
  have key : ∀ i : g.Species,
      g.prodOf wp.inducer i (fun s => x (e.symm s)) = wp.γ i * x (e.symm i) := by
    intro i
    obtain ⟨k, rfl⟩ := e.surjective i
    have hk := congrFun hx k
    simp only [GRN.Dynamics.field_apply, GRN.assembledProd, Pi.zero_apply] at hk
    rw [Equiv.symm_apply_apply]
    linarith [hk]
  have hsteady : (g.toSystem hac wp).IsSteady (fun s => x (e.symm s)) := key
  have huniq :=
    (g.toSystem hac wp).steady_unique hsteady (g.toSystem hac wp).steadyPoint_isSteady
  funext k
  have hk2 := congrFun huniq (e k)
  simp only [Equiv.symm_apply_apply] at hk2
  exact hk2

end GRN
