import Mathlib
import GRN.Dynamics.Feedforward
import GRN.Dynamics.Sensor

/-!
# A real two-stage Hill cascade through the constructive machinery

Validates the `FeedforwardSystem` IR on an actual Hill-kinetic sensor cascade (not a constant production):
an external inducer drives species 0 via a Hill response, which drives the reporter species 1 via another.
It discharges the `local'` and `nonneg` obligations from genuine `hill` kinetics and concludes a unique
steady state through `exists_unique_steady`: the constructive functor's target, exercised end to end.
-/

namespace GRN.Dynamics

/-- A two-stage inducible Hill cascade: `ind → (hill) → x₀ → (hill) → x₁`. -/
structure Cascade2 where
  ind : ℝ
  γ0 : ℝ
  γ1 : ℝ
  a0 : ℝ
  a1 : ℝ
  K0 : ℝ
  n0 : ℝ
  b0 : ℝ
  b1 : ℝ
  K1 : ℝ
  n1 : ℝ
  hind : 0 ≤ ind
  hγ0 : 0 < γ0
  hγ1 : 0 < γ1
  hK0 : 0 < K0
  hK1 : 0 < K1
  ha0 : 0 ≤ a0
  ha1 : 0 ≤ a1
  hb0 : 0 ≤ b0
  hb1 : 0 ≤ b1

/-- The cascade as a feedforward system over `Fin 2` ordered by `<` (which is well-founded). -/
noncomputable def Cascade2.toSystem (C : Cascade2) : FeedforwardSystem (Fin 2) (· < ·) where
  wf := wellFounded_lt
  γ := ![C.γ0, C.γ1]
  hγ := by
    intro i
    fin_cases i
    · simpa using C.hγ0
    · simpa using C.hγ1
  prod := fun i x => ![hill C.a0 C.a1 C.K0 C.n0 C.ind, hill C.b0 C.b1 C.K1 C.n1 (x 0)] i
  local' := by
    intro i x y hxy
    fin_cases i
    · simp
    · have hx0 : x 0 = y 0 := hxy 0 (by decide)
      simp [hx0]
  nonneg := by
    intro i x hx
    fin_cases i
    · simpa using hill_nonneg C.hK0 C.ha0 C.ha1 C.ind C.hind
    · simpa using hill_nonneg C.hK1 C.hb0 C.hb1 (x 0) (hx 0)

/-- **A two-stage Hill sensor cascade has a unique steady state**, through the constructive IR. -/
theorem Cascade2.unique_steady (C : Cascade2) : ∃! x, C.toSystem.IsSteady x :=
  C.toSystem.exists_unique_steady

end GRN.Dynamics
