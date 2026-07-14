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

/-- **Parallel-edge sign consistency.** Any two interaction-graph edges sharing a source and a target
carry the same sign, so `graphEdgeSign` (which reads the first matching edge) is well-defined: it is the
sign of *every* edge between that ordered pair. This is the honest minimal condition compatible with the
negative feedback loops a switch carries — unlike full sign-consistency (balance), which would force
acyclicity and make the switch theorem degenerate. -/
def EdgeSignConsistent (g : GRN) : Prop :=
  ∀ e₁ ∈ signedInteractionGraph g, ∀ e₂ ∈ signedInteractionGraph g,
    e₁.1 = e₂.1 → e₁.2.1 = e₂.2.1 → e₁.2.2 = e₂.2.2

/-- Under `hmono`, a nonzero interaction-graph edge sign is `±1`. -/
private lemma graphEdgeSign_eq_one_or_neg_one (g : GRN) (src dst : String)
    (hmono : ∀ edge ∈ signedInteractionGraph g, edge.2.2 = 1 ∨ edge.2.2 = -1)
    (h : graphEdgeSign g src dst ≠ 0) :
    graphEdgeSign g src dst = 1 ∨ graphEdgeSign g src dst = -1 := by
  unfold graphEdgeSign at h ⊢
  cases hf : (g.signedInteractionGraph).find? (fun ed => ed.1 == src && ed.2.1 == dst) with
  | none => rw [hf] at h; simp at h
  | some ed =>
    have hmem : ed ∈ signedInteractionGraph g := List.mem_of_find?_eq_some hf
    exact hmono ed hmem

/-! ## Layer 1 — concrete signed derivatives of the interpreted rates

Each lemma exposes the pointwise derivative and pins its sign at a strictly positive input. -/

-- UNIT: hill-deriv-sign  (analytic; globally monotone, tractable)
/-- **Single-input Hill derivative sign.** At a strictly positive input the derivative of the Hill
response exists and its sign is `pairSign a0 a1`: positive when `a0 < a1` (activation), negative when
`a1 < a0` (repression), zero when `a0 = a1`. Globally monotone, so the sign is context-free. -/
theorem hill_hasDerivAt_sign (a0 a1 K n u : ℝ) (hK : 0 < K) (hn : 0 < n) (hu : 0 < u) :
    ∃ d : ℝ, HasDerivAt (fun t => hill a0 a1 K n t) d u ∧
      (a0 < a1 → 0 < d) ∧ (a1 < a0 → d < 0) ∧ (a0 = a1 → d = 0) := by
  have huK : (0 : ℝ) < u / K := div_pos hu hK
  have hRpos : (0 : ℝ) < (u / K) ^ n := Real.rpow_pos_of_pos huK n
  have hrp : (0 : ℝ) < (u / K) ^ (n - 1) := Real.rpow_pos_of_pos huK (n - 1)
  -- The composite `t ↦ (t / K) ^ n` via the `rpow` chain rule on the inner map `t ↦ t / K`.
  have hinner : HasDerivAt (fun t : ℝ => t / K) (1 / K) u := by
    simpa using (hasDerivAt_id u).div_const K
  have hfpow : HasDerivAt (fun t : ℝ => (t / K) ^ n)
      (1 / K * n * (u / K) ^ (n - 1)) u := hinner.rpow_const (Or.inl (ne_of_gt huK))
  -- Numerator `a0 + a1·(t/K)ⁿ` and denominator `1 + (t/K)ⁿ` of the Hill response.
  have hN : HasDerivAt (fun t : ℝ => a0 + a1 * (t / K) ^ n)
      (a1 * (1 / K * n * (u / K) ^ (n - 1))) u := (hfpow.const_mul a1).const_add a0
  have hD : HasDerivAt (fun t : ℝ => 1 + (t / K) ^ n)
      (1 / K * n * (u / K) ^ (n - 1)) u := hfpow.const_add 1
  have hD0 : (fun t : ℝ => 1 + (t / K) ^ n) u ≠ 0 := by
    show (1 : ℝ) + (u / K) ^ n ≠ 0
    have : (0 : ℝ) < 1 + (u / K) ^ n := by linarith
    exact this.ne'
  -- The scalar coefficient `(1/K)·n·(u/K)^{n-1} / (1+(u/K)ⁿ)²` is strictly positive, so the quotient
  -- rule's derivative reduces to that coefficient times `a1 - a0`, pinning its sign.
  have hfp_pos : (0 : ℝ) < 1 / K * n * (u / K) ^ (n - 1) :=
    mul_pos (mul_pos (one_div_pos.mpr hK) hn) hrp
  have hden : (0 : ℝ) < (1 + (u / K) ^ n) ^ 2 :=
    pow_pos (by linarith : (0 : ℝ) < 1 + (u / K) ^ n) 2
  have hC : (0 : ℝ) < 1 / K * n * (u / K) ^ (n - 1) / (1 + (u / K) ^ n) ^ 2 :=
    div_pos hfp_pos hden
  refine ⟨1 / K * n * (u / K) ^ (n - 1) / (1 + (u / K) ^ n) ^ 2 * (a1 - a0),
    ?_, ?_, ?_, ?_⟩
  · have hdiv := hN.div hD hD0
    have hval : (a1 * (1 / K * n * (u / K) ^ (n - 1)) * (1 + (u / K) ^ n)
          - (a0 + a1 * (u / K) ^ n) * (1 / K * n * (u / K) ^ (n - 1)))
            / (1 + (u / K) ^ n) ^ 2
        = 1 / K * n * (u / K) ^ (n - 1) / (1 + (u / K) ^ n) ^ 2 * (a1 - a0) := by
      ring
    simp only [hill]
    rw [← hval]
    exact hdiv
  · intro h
    exact mul_pos hC (by linarith)
  · intro h
    exact mul_neg_of_pos_of_neg hC (by linarith)
  · intro h
    have : a1 - a0 = 0 := by linarith
    rw [this, mul_zero]

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
  -- The two regulator responses `r₁ = (u₁/K₁)^{n₁}` and `r₂ = (u₂/K₂)^{n₂}` are strictly positive.
  have hR1 : (0:ℝ) < (u1 / K1) ^ n1 := Real.rpow_pos_of_pos (div_pos hu1 hK1) n1
  have hR2 : (0:ℝ) < (u2 / K2) ^ n2 := Real.rpow_pos_of_pos (div_pos hu2 hK2) n2
  -- Derivative of the inner power `t ↦ (t/K₁)^{n₁}` at `u₁`.
  have hbase : HasDerivAt (fun t : ℝ => t / K1) (1 / K1) u1 := (hasDerivAt_id u1).div_const K1
  have hg : HasDerivAt (fun t : ℝ => (t / K1) ^ n1) (1 / K1 * n1 * (u1 / K1) ^ (n1 - 1)) u1 :=
    hbase.rpow_const (Or.inl (ne_of_gt (div_pos hu1 hK1)))
  -- `dg`, the value of that derivative, is strictly positive.
  have hdg : (0:ℝ) < 1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) :=
    mul_pos (mul_pos (one_div_pos.mpr hK1) hn1) (Real.rpow_pos_of_pos (div_pos hu1 hK1) _)
  -- Derivatives of the numerator and denominator of `hill2` in the first input.
  have hN := (((hg.const_mul a1).const_add a0).add_const (a2 * (u2 / K2) ^ n2)).add
    ((hg.mul_const ((u2 / K2) ^ n2)).const_mul a3)
  have hD := ((hg.const_add (1 : ℝ)).add_const ((u2 / K2) ^ n2)).add
    (hg.mul_const ((u2 / K2) ^ n2))
  have hDval : (0:ℝ) <
      1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2 := by positivity
  have hDne : (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2) ≠ 0 :=
    ne_of_gt hDval
  have h := hN.div hD hDne
  -- Closed-form derivative: sign is carried by `(a1 - a0) + (a3 - a2)·r₂`.
  refine ⟨1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) * (1 + (u2 / K2) ^ n2)
      * ((a1 - a0) + (a3 - a2) * (u2 / K2) ^ n2)
      / (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2) ^ 2, ?_, ?_, ?_⟩
  · -- The named scalar is the quotient-rule derivative of `hill2` in its first input,
    -- after the numerator cancellation `(a1 + a3·r₂)·D − N·(1 + r₂) = (1 + r₂)·((a1−a0)+(a3−a2)·r₂)`.
    have hval : 1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) * (1 + (u2 / K2) ^ n2)
          * ((a1 - a0) + (a3 - a2) * (u2 / K2) ^ n2)
          / (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2) ^ 2
        = ((a1 * (1 / K1 * n1 * (u1 / K1) ^ (n1 - 1))
              + a3 * (1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) * (u2 / K2) ^ n2))
            * (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2)
            - (a0 + a1 * (u1 / K1) ^ n1 + a2 * (u2 / K2) ^ n2
                + a3 * ((u1 / K1) ^ n1 * (u2 / K2) ^ n2))
              * (1 / K1 * n1 * (u1 / K1) ^ (n1 - 1)
                + 1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) * (u2 / K2) ^ n2))
          / (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2) ^ 2 := by
      field_simp
      ring
    rw [hval]; exact h
  · -- Monotone-activating left port ⇒ strictly positive derivative.
    rintro ⟨h01, h23, hstrict⟩
    apply div_pos
    · have hX : (0:ℝ) < 1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) * (1 + (u2 / K2) ^ n2) :=
        mul_pos hdg (by positivity)
      have hbr : (0:ℝ) < (a1 - a0) + (a3 - a2) * (u2 / K2) ^ n2 := by
        rcases hstrict with h | h
        · have h1 : (0:ℝ) < a1 - a0 := by linarith
          have h2 : (0:ℝ) ≤ (a3 - a2) * (u2 / K2) ^ n2 := mul_nonneg (by linarith) hR2.le
          linarith
        · have h1 : (0:ℝ) ≤ a1 - a0 := by linarith
          have h2 : (0:ℝ) < (a3 - a2) * (u2 / K2) ^ n2 := mul_pos (by linarith) hR2
          linarith
      exact mul_pos hX hbr
    · positivity
  · -- Monotone-repressing left port ⇒ strictly negative derivative.
    rintro ⟨h01, h23, hstrict⟩
    apply div_neg_of_neg_of_pos
    · have hX : (0:ℝ) < 1 / K1 * n1 * (u1 / K1) ^ (n1 - 1) * (1 + (u2 / K2) ^ n2) :=
        mul_pos hdg (by positivity)
      have hbr : (a1 - a0) + (a3 - a2) * (u2 / K2) ^ n2 < 0 := by
        rcases hstrict with h | h
        · have h1 : a1 - a0 < 0 := by linarith
          have h2 : (a3 - a2) * (u2 / K2) ^ n2 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (by linarith) hR2.le
          linarith
        · have h1 : a1 - a0 ≤ 0 := by linarith
          have h2 : (a3 - a2) * (u2 / K2) ^ n2 < 0 := mul_neg_of_neg_of_pos (by linarith) hR2
          linarith
      exact mul_neg_of_pos_of_neg hX hbr
    · positivity

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
  -- Strict positivity of the two normalized inputs and of `1 + r₁`.
  have huK2 : (0 : ℝ) < u2 / K2 := div_pos hu2 hK2
  have hRpos : (0 : ℝ) < (u1 / K1) ^ n1 := Real.rpow_pos_of_pos (div_pos hu1 hK1) n1
  have hSpos : (0 : ℝ) < (u2 / K2) ^ n2 := Real.rpow_pos_of_pos huK2 n2
  have h1R : (0 : ℝ) < 1 + (u1 / K1) ^ n1 := by linarith
  -- The co-input power `(t/K2)^n2` has a strictly positive derivative at `u2`.
  obtain ⟨sD, hsDpos, hs⟩ :
      ∃ sD, 0 < sD ∧ HasDerivAt (fun t => (t / K2) ^ n2) sD u2 := by
    have hbase : HasDerivAt (fun t : ℝ => t / K2) (1 / K2) u2 :=
      (hasDerivAt_id u2).div_const K2
    refine ⟨_, ?_, hbase.rpow_const (Or.inl huK2.ne')⟩
    exact mul_pos (mul_pos (one_div_pos.mpr hK2) hn2) (Real.rpow_pos_of_pos huK2 (n2 - 1))
  -- Derivatives of the numerator and denominator of `hill2` in the second input.
  have hnum : HasDerivAt
      (fun t => a0 + a1 * (u1 / K1) ^ n1 + a2 * (t / K2) ^ n2 +
        a3 * ((u1 / K1) ^ n1 * (t / K2) ^ n2))
      (0 + a2 * sD + a3 * ((u1 / K1) ^ n1 * sD)) u2 :=
    (((hasDerivAt_const u2 (a0 + a1 * (u1 / K1) ^ n1)).add (hs.const_mul a2)).add
      ((hs.const_mul ((u1 / K1) ^ n1)).const_mul a3))
  have hden : HasDerivAt
      (fun t => 1 + (u1 / K1) ^ n1 + (t / K2) ^ n2 + (u1 / K1) ^ n1 * (t / K2) ^ n2)
      (0 + sD + (u1 / K1) ^ n1 * sD) u2 :=
    (((hasDerivAt_const u2 (1 + (u1 / K1) ^ n1)).add hs).add (hs.const_mul ((u1 / K1) ^ n1)))
  have hDenpos : (0 : ℝ) <
      1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2 := by
    nlinarith [mul_pos hRpos hSpos]
  have hderiv : HasDerivAt (fun t => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 t)
      (((0 + a2 * sD + a3 * ((u1 / K1) ^ n1 * sD)) *
            (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2) -
          (a0 + a1 * (u1 / K1) ^ n1 + a2 * (u2 / K2) ^ n2 + a3 * ((u1 / K1) ^ n1 * (u2 / K2) ^ n2)) *
            (0 + sD + (u1 / K1) ^ n1 * sD)) /
        (1 + (u1 / K1) ^ n1 + (u2 / K2) ^ n2 + (u1 / K1) ^ n1 * (u2 / K2) ^ n2) ^ 2) u2 := by
    simp only [hill2]
    exact hnum.div hden hDenpos.ne'
  refine ⟨_, hderiv, ?_, ?_⟩
  · -- Activating right port: sign of `(a2 − a0) + (a3 − a1)·r₁` is positive.
    rintro ⟨h02, h13, hstrict⟩
    have hfac : (0 : ℝ) < (a2 - a0) + (a3 - a1) * (u1 / K1) ^ n1 := by
      rcases hstrict with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h13) hRpos.le]
      · nlinarith [mul_pos (sub_pos.2 h) hRpos]
    have hprod :
        0 < sD * (1 + (u1 / K1) ^ n1) * ((a2 - a0) + (a3 - a1) * (u1 / K1) ^ n1) :=
      mul_pos (mul_pos hsDpos h1R) hfac
    apply div_pos
    · nlinarith [hprod]
    · exact pow_pos hDenpos 2
  · -- Repressing right port: sign of `(a2 − a0) + (a3 − a1)·r₁` is negative.
    rintro ⟨h20, h31, hstrict⟩
    have hfac : (a2 - a0) + (a3 - a1) * (u1 / K1) ^ n1 < 0 := by
      rcases hstrict with h | h
      · nlinarith [mul_nonneg (sub_nonneg.2 h31) hRpos.le]
      · nlinarith [mul_pos (sub_pos.2 h) hRpos]
    have hprod :
        sD * (1 + (u1 / K1) ^ n1) * ((a2 - a0) + (a3 - a1) * (u1 / K1) ^ n1) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hsDpos h1R) hfac
    apply div_neg_of_neg_of_pos
    · nlinarith [hprod]
    · exact pow_pos hDenpos 2

-- UNIT: sum-deriv-sign  (analytic; per-input summand reuses `hill`)
/-- **`sum`-operator per-input derivative sign.** A `sum` summand is a single-input Hill in one input
only, so the port derivative reuses the `hill` sign: nonnegative on an activating summand
(`a0 ≤ a1`), matching the `+1` sign `operatorInputSigns` assigns every `sum` port. -/
theorem sum_summand_hasDerivAt_nonneg (a0 a1 K n u : ℝ)
    (hK : 0 < K) (hn : 0 < n) (hu : 0 < u) (ha : a0 ≤ a1) :
    ∃ d : ℝ, HasDerivAt (fun t => hill a0 a1 K n t) d u ∧ 0 ≤ d := by
  have hbase : (0 : ℝ) < u / K := div_pos hu hK
  have hdiv : HasDerivAt (fun t : ℝ => t / K) (1 / K) u :=
    (hasDerivAt_id u).div_const K
  have hr : HasDerivAt (fun t : ℝ => (t / K) ^ n)
      (1 / K * n * (u / K) ^ (n - 1)) u :=
    hdiv.rpow_const (Or.inl hbase.ne')
  have hnum : HasDerivAt (fun t : ℝ => a0 + a1 * (t / K) ^ n)
      (a1 * (1 / K * n * (u / K) ^ (n - 1))) u :=
    (hr.const_mul a1).const_add a0
  have hden : HasDerivAt (fun t : ℝ => 1 + (t / K) ^ n)
      (1 / K * n * (u / K) ^ (n - 1)) u := hr.const_add 1
  have hrnn : (0 : ℝ) ≤ (u / K) ^ n := (Real.rpow_pos_of_pos hbase n).le
  have hpos : (0 : ℝ) < 1 + (u / K) ^ n := by linarith
  have key : HasDerivAt (fun t => hill a0 a1 K n t)
      ((a1 * (1 / K * n * (u / K) ^ (n - 1)) * (1 + (u / K) ^ n)
          - (a0 + a1 * (u / K) ^ n) * (1 / K * n * (u / K) ^ (n - 1)))
        / (1 + (u / K) ^ n) ^ 2) u :=
    hnum.div hden hpos.ne'
  refine ⟨_, key, ?_⟩
  rw [show (a1 * (1 / K * n * (u / K) ^ (n - 1)) * (1 + (u / K) ^ n)
            - (a0 + a1 * (u / K) ^ n) * (1 / K * n * (u / K) ^ (n - 1)))
          / (1 + (u / K) ^ n) ^ 2
        = (a1 - a0) * (1 / K * n * (u / K) ^ (n - 1)) / (1 + (u / K) ^ n) ^ 2 from by
      ring]
  have hr'pos : (0 : ℝ) < 1 / K * n * (u / K) ^ (n - 1) :=
    mul_pos (mul_pos (one_div_pos.mpr hK) hn) (Real.rpow_pos_of_pos hbase _)
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha) hr'pos.le) (by positivity)

/-! ### Repressing two-input Hill monotonicity and interaction-sign decoders

The entry-sign assembly compares the interpreted rate at the base point against the `c`-axis-perturbed
point. A repressing `hill2` port is antitone in that input; a monotone `±1`/`0`/absent port sign is read
back to real inequalities on the Hill levels. -/

/-- The two-input Hill response is antitone in its first input when it represses in both contexts
(`a1 ≤ a0` and `a3 ≤ a2`). -/
private theorem hill2_antitoneOn_left {a0 a1 a2 a3 K1 K2 n1 n2 u2 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn1 : 0 ≤ n1) (hu2 : 0 ≤ u2)
    (ha : a1 ≤ a0) (ha' : a3 ≤ a2) :
    AntitoneOn (fun u1 => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  simp only [hill2]
  set r2 := (u2 / K2) ^ n2
  set ru := (u / K1) ^ n1
  set rv := (v / K1) ^ n1
  have hr2 : 0 ≤ r2 := Real.rpow_nonneg (div_nonneg hu2 hK2.le) n2
  have hru : 0 ≤ ru := Real.rpow_nonneg (div_nonneg hu hK1.le) n1
  have hrle : ru ≤ rv := by
    apply Real.rpow_le_rpow (div_nonneg hu hK1.le) _ hn1
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right huv (inv_pos.2 hK1).le
  have hrv : 0 ≤ rv := le_trans hru hrle
  have hdu : (0:ℝ) < 1 + ru + r2 + ru * r2 := by nlinarith [mul_nonneg hru hr2]
  have hdv : (0:ℝ) < 1 + rv + r2 + rv * r2 := by nlinarith [mul_nonneg hrv hr2]
  rw [← sub_nonneg, div_sub_div _ _ (ne_of_gt hdu) (ne_of_gt hdv)]
  apply div_nonneg
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle)) hr2,
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr2) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr2) hr2) (sub_nonneg.2 hrle)]
  · exact (mul_pos hdu hdv).le

/-- The two-input Hill response is antitone in its second input when it represses in both contexts
(`a2 ≤ a0` and `a3 ≤ a1`). -/
private theorem hill2_antitoneOn_right {a0 a1 a2 a3 K1 K2 n1 n2 u1 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 < K2) (hn2 : 0 ≤ n2) (hu1 : 0 ≤ u1)
    (ha : a2 ≤ a0) (ha' : a3 ≤ a1) :
    AntitoneOn (fun u2 => hill2 a0 a1 a2 a3 K1 K2 n1 n2 u1 u2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  simp only [hill2]
  set r1 := (u1 / K1) ^ n1
  set ru := (u / K2) ^ n2
  set rv := (v / K2) ^ n2
  have hr1 : 0 ≤ r1 := Real.rpow_nonneg (div_nonneg hu1 hK1.le) n1
  have hru : 0 ≤ ru := Real.rpow_nonneg (div_nonneg hu hK2.le) n2
  have hrle : ru ≤ rv := by
    apply Real.rpow_le_rpow (div_nonneg hu hK2.le) _ hn2
    rw [div_eq_mul_inv, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right huv (inv_pos.2 hK2).le
  have hrv : 0 ≤ rv := le_trans hru hrle
  have hdu : (0:ℝ) < 1 + r1 + ru + r1 * ru := by nlinarith [mul_nonneg hr1 hru]
  have hdv : (0:ℝ) < 1 + r1 + rv + r1 * rv := by nlinarith [mul_nonneg hr1 hrv]
  rw [← sub_nonneg, div_sub_div _ _ (ne_of_gt hdu) (ne_of_gt hdv)]
  apply div_nonneg
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hrle)) hr1,
      mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr1) (sub_nonneg.2 hrle),
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ha') hr1) hr1) (sub_nonneg.2 hrle)]
  · exact (mul_pos hdu hdv).le

/-- With coincident basal/saturation levels a single-input Hill response is the flat value `a0` on the
nonnegative input domain. -/
private lemma hill_flat {a0 a1 K n u : ℝ} (hK : 0 < K) (hu : 0 ≤ u) (ha : a0 = a1) :
    hill a0 a1 K n u = a0 := by
  subst ha
  have hr : (0 : ℝ) ≤ (u / K) ^ n := Real.rpow_nonneg (div_nonneg hu hK.le) n
  have hden : (0 : ℝ) < 1 + (u / K) ^ n := by linarith
  simp only [hill]
  rw [div_eq_iff (ne_of_gt hden)]; ring

/-- A `+1` single-input port sign forces a strictly activating level pair. -/
private lemma pairSign_eq_one {q0 q1 : ℚ} (h : pairSign q0 q1 = some 1) : q0 < q1 := by
  unfold pairSign at h; split_ifs at h with h1 h2 <;> simp_all

/-- A `-1` single-input port sign forces a strictly repressing level pair. -/
private lemma pairSign_eq_neg_one {q0 q1 : ℚ} (h : pairSign q0 q1 = some (-1)) : q1 < q0 := by
  unfold pairSign at h; split_ifs at h with h1 h2 <;> simp_all

/-- An absent single-input port sign forces coincident levels. -/
private lemma pairSign_eq_none {q0 q1 : ℚ} (h : pairSign q0 q1 = none) : q0 = q1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [pairSign, if_pos hlt] at h; simp at h
  · rw [pairSign, if_neg (not_lt.mpr hgt.le), if_pos hgt] at h; simp at h

/-- A pair for which an `any`-over-decide flag is `false` fails the underlying relation. -/
private lemma not_rel_of_any_false {pairs : List (ℚ × ℚ)} {r : ℚ → ℚ → Prop}
    [∀ a b, Decidable (r a b)] (hf : (pairs.any fun q => decide (r q.1 q.2)) = false)
    (p : ℚ × ℚ) (hp : p ∈ pairs) : ¬ r p.1 p.2 := by
  intro hr
  have : (pairs.any fun q => decide (r q.1 q.2)) = true :=
    List.any_eq_true.mpr ⟨p, hp, by simpa using hr⟩
  rw [this] at hf; simp at hf

/-- A `+1` monotone port sign makes every level pair weakly activating. -/
private lemma signFromPairs_one {pairs : List (ℚ × ℚ)} (h : signFromPairs pairs = some 1) :
    ∀ p ∈ pairs, p.1 ≤ p.2 := by
  have hn : (pairs.any fun q => decide (q.2 < q.1)) = false := by
    rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.2 < q.1)) with hc | hc
    · exfalso
      rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.1 < q.2)) with hp2 | hp2 <;>
        simp [signFromPairs, hc, hp2] at h
    · exact hc
  intro p hp
  exact not_lt.mp (not_rel_of_any_false (r := fun a b => b < a) hn p hp)

/-- A `-1` monotone port sign makes every level pair weakly repressing. -/
private lemma signFromPairs_neg {pairs : List (ℚ × ℚ)} (h : signFromPairs pairs = some (-1)) :
    ∀ p ∈ pairs, p.2 ≤ p.1 := by
  have hn : (pairs.any fun q => decide (q.1 < q.2)) = false := by
    rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.1 < q.2)) with hc | hc
    · exfalso
      rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.2 < q.1)) with hp2 | hp2 <;>
        simp [signFromPairs, hc, hp2] at h
    · exact hc
  intro p hp
  exact not_lt.mp (not_rel_of_any_false (r := fun a b => a < b) hn p hp)

/-- An absent monotone port sign makes every level pair coincident. -/
private lemma signFromPairs_none {pairs : List (ℚ × ℚ)} (h : signFromPairs pairs = none) :
    ∀ p ∈ pairs, p.1 = p.2 := by
  have hpos : (pairs.any fun q => decide (q.1 < q.2)) = false := by
    rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.1 < q.2)) with hc | hc
    · exfalso
      rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.2 < q.1)) with hp2 | hp2 <;>
        simp [signFromPairs, hc, hp2] at h
    · exact hc
  have hneg : (pairs.any fun q => decide (q.2 < q.1)) = false := by
    rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.2 < q.1)) with hc | hc
    · exfalso
      rcases Bool.eq_false_or_eq_true (pairs.any fun q => decide (q.1 < q.2)) with hp2 | hp2 <;>
        simp [signFromPairs, hc, hp2] at h
    · exact hc
  intro p hp
  exact le_antisymm (not_lt.mp (not_rel_of_any_false (r := fun a b => b < a) hneg p hp))
    (not_lt.mp (not_rel_of_any_false (r := fun a b => a < b) hpos p hp))

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
  -- Any Fréchet derivative at `z` exists (`hasFDerivAt_assembledProd`) and all such are equal, so the
  -- concrete `c`-directional scalar is read off a fixed derivative `E₀` and shared by every `E`.
  obtain ⟨E₀, hE₀⟩ := g.hasFDerivAt_assembledProd wp hreg e z hz
  refine ⟨E₀ (Pi.single c (1 : ℝ)) r, ?_, ?_⟩
  · -- The `c`-axis derivative of coordinate `r`: project the composition of `E₀` with the affine line.
    set v : Fin n → ℝ := Pi.single c (1 : ℝ) with hv
    have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
      exact h1.const_add z
    have hcomp : HasDerivAt (fun t : ℝ => g.assembledProd wp e (z + t • v)) (E₀ v) 0 :=
      HasFDerivAt.comp_hasDerivAt_of_eq (f := fun t : ℝ => z + t • v) (x := (0 : ℝ))
        hE₀ hline (by simp)
    exact HasFDerivAt.comp_hasDerivAt_of_eq
      (f := fun t : ℝ => g.assembledProd wp e (z + t • v)) (x := (0 : ℝ))
      (ContinuousLinearMap.proj r : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt hcomp rfl
  · -- Any Fréchet derivative equals `E₀`, so its `(r, c)` entry is that same scalar.
    intro E hE
    rw [hE.unique hE₀]
    simp only [jacobianMatrix, LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]

/-! ### Enumerated-cycle membership of a self-loop

A `+1` self-loop is a length-one positive cycle. Recording its sign inside `cycleSignsEdges` bridges a
positive self-regulation edge to `hasPositiveLoopEdges`, which `negJac_diag_pos` rules out. -/

private theorem js_raw_mem (E : List SignedEdge) (x : String) :
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

private theorem js_dedup_mem (raw : List String) (x : String) :
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

private theorem js_verticesOf_mem (E : List SignedEdge) (x : String) :
    x ∈ verticesOf E ↔ ∃ e ∈ E, x = e.1 ∨ x = e.2.1 := by
  rw [verticesOf, js_dedup_mem, js_raw_mem]

private theorem js_mem_neighbors (E : List SignedEdge) (u b : String) (s : Int) (h : (u, b, s) ∈ E) :
    (b, s) ∈ neighbors E u := by
  simp only [neighbors, List.mem_filterMap]
  exact ⟨(u, b, s), h, by simp⟩

/-- An element that a `List.foldr` step `f a` always emits (regardless of the accumulator) is in the
fold when `a` occurs in the list, provided every step retains its accumulator. -/
private theorem js_mem_foldr_of_step {α β : Type*} (f : α → List β → List β)
    (hmono : ∀ a acc, (acc : List β) ⊆ f a acc) (init : List β)
    (L : List α) (a : α) (ha : a ∈ L) (x : β) (hx : ∀ acc, x ∈ f a acc) :
    x ∈ List.foldr f init L := by
  induction L with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | hmem
    · simpa only [List.foldr_cons] using hx _
    · simp only [List.foldr_cons]; exact hmono b _ (ih hmem)

/-- A self-edge's sign is one of the enumerated cycle signs: the length-one directed cycle at its
vertex records `1 · sign` in the DFS. -/
private theorem selfEdge_sign_mem_cycleSignsEdges (E : List SignedEdge) (v : String) (s : Int)
    (he : (v, v, s) ∈ E) : s ∈ cycleSignsEdges E := by
  have hvmem : v ∈ verticesOf E := (js_verticesOf_mem E v).mpr ⟨(v, v, s), he, Or.inl rfl⟩
  have hnb : (v, s) ∈ neighbors E v := js_mem_neighbors E v v s he
  have hinner : s ∈ cycleSignsEdges.dfs E ((verticesOf E).length + 1) v v [v] 1 := by
    simp only [cycleSignsEdges.dfs]
    refine js_mem_foldr_of_step _ ?_ [] (neighbors E v) (v, s) hnb s ?_
    · intro nb acc x hx
      by_cases h1 : (nb.1 == v) = true
      · rw [if_pos h1]; exact List.mem_cons_of_mem _ hx
      · rw [if_neg h1]
        by_cases h2 : ([v].any (· == nb.1)) = true
        · rw [if_pos h2]; exact hx
        · rw [if_neg h2]; exact List.mem_append_right _ hx
    · intro acc
      have hcond : ((v, s).1 == v) = true := by simp
      rw [if_pos hcond]; simp
  rw [cycleSignsEdges]
  refine js_mem_foldr_of_step _ ?_ [] (verticesOf E) v hvmem s ?_
  · intro w acc x hx; exact List.mem_append_right _ hx
  · intro acc; exact List.mem_append_left _ hinner

/-! ### Sign of a derivative from one-sided monotonicity

The `c`-directional derivative of the assembled production is signed by comparing the production at the
base point against nearby perturbed points: rightward monotonicity forces a nonnegative derivative,
rightward antitonicity a nonpositive one, and a locally constant map a zero derivative. -/

private lemma ent_deriv_nonneg_of_right {f : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt f d 0)
    (h : ∀ t, 0 ≤ t → f 0 ≤ f t) : 0 ≤ d := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hsub : Set.Ioi (0 : ℝ) ⊆ {x : ℝ | x ≠ 0} := fun x hx => ne_of_gt hx
  have htend : Filter.Tendsto (slope f 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hd.mono_left (nhdsWithin_mono 0 hsub)
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [slope_def_field]
  exact div_nonneg (by linarith [h x hx0.le]) (by linarith)

private lemma ent_deriv_nonpos_of_right {f : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt f d 0)
    (h : ∀ t, 0 ≤ t → f t ≤ f 0) : d ≤ 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have hsub : Set.Ioi (0 : ℝ) ⊆ {x : ℝ | x ≠ 0} := fun x hx => ne_of_gt hx
  have htend : Filter.Tendsto (slope f 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hd.mono_left (nhdsWithin_mono 0 hsub)
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [h x hx0.le]) (by linarith)

private lemma ent_deriv_eq_zero_of_const {f : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt f d 0)
    (h : ∀ t, f t = f 0) : d = 0 := by
  have hconst : HasDerivAt f 0 0 := by
    have : f = fun _ => f 0 := funext h
    rw [this]; exact hasDerivAt_const 0 (f 0)
  exact hd.unique hconst

/-! ### Structural bridges for the entry-sign proof -/

/-- A `some v` port at index `p`, walked in lockstep with its input `src`, emits the edge
`(src, dst, v)` to every output `dst`. -/
private lemma ent_edgesFrom_mem : ∀ (ss : List (Option Int)) (is outs : List String) (p : ℕ)
    (v : Int) (src dst : String),
    ss[p]? = some (some v) → is[p]? = some src → dst ∈ outs →
    (src, dst, v) ∈ edgesFrom ss is outs := by
  intro ss
  induction ss with
  | nil => intro is outs p v src dst hss _ _; simp at hss
  | cons s ss' ih =>
    intro is outs p v src dst hss his hd
    cases is with
    | nil => cases p <;> simp at his
    | cons i is' =>
      cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hss his
        subst hss; subst his
        simp only [edgesFrom, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨dst, hd, rfl⟩)
      | succ p =>
        simp only [List.getElem?_cons_succ] at hss his
        simp only [edgesFrom, List.mem_append]
        exact Or.inr (ih is' outs p v src dst hss his hd)

/-- An edge emitted by an operator's lockstep walk belongs to the interaction graph. -/
private lemma ent_mem_signedInteractionGraph (g : GRN) (op : Node) (ed : SignedEdge)
    (hop : op ∈ g.operators)
    (hmem : ed ∈ edgesFrom (g.opEdgeSigns op) (g.inputsOf op.id) (g.outputsOf op.id)) :
    ed ∈ signedInteractionGraph g := by
  rw [signedInteractionGraph]
  have gen : ∀ L, op ∈ L → ed ∈ opEdges g L := by
    intro L
    induction L with
    | nil => intro h; simp at h
    | cons a t ih =>
      intro hL
      simp only [opEdges, List.mem_append]
      rcases List.mem_cons.mp hL with rfl | hmt
      · exact Or.inl hmem
      · exact Or.inr (ih hmt)
  exact gen g.operators hop

/-- Under parallel-edge consistency, any edge of the interaction graph carries the sign that
`graphEdgeSign` reports for its endpoints. -/
private lemma ent_graphEdgeSign_eq_of_mem (g : GRN) (hconsist : EdgeSignConsistent g)
    (src dst : String) (v : Int)
    (hmem : (src, dst, v) ∈ signedInteractionGraph g) : graphEdgeSign g src dst = v := by
  unfold graphEdgeSign
  cases hf : (g.signedInteractionGraph).find? (fun ed => ed.1 == src && ed.2.1 == dst) with
  | none =>
    exfalso
    have := (List.find?_eq_none.mp hf) (src, dst, v) hmem
    simp at this
  | some ed =>
    have hedmem : ed ∈ signedInteractionGraph g := List.mem_of_find?_eq_some hf
    have hcond := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact hconsist ed hedmem (src, dst, v) hmem hcond.1 hcond.2

/-- The value fed to each input under the `c`-axis perturbation: only the coordinate of species `e c`
moves, at unit rate. -/
private lemma ent_valuation_perturb (g : GRN) (inducer : String → ℝ) {n : ℕ} (e : Fin n ≃ g.Species)
    (z : Fin n → ℝ) (c : Fin n) (t : ℝ) (id : String) :
    g.valuation inducer (fun j => (z + t • Pi.single c (1 : ℝ) : Fin n → ℝ) (e.symm j)) id
      = g.valuation inducer (fun j => z (e.symm j)) id + t * (if id = (e c : String) then 1 else 0) := by
  unfold valuation
  by_cases hid : id ∈ g.regIds
  · simp only [dif_pos hid, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hc : id = (e c : String)
    · have hsc : e.symm ⟨id, hid⟩ = c := e.symm_apply_eq.mpr (Subtype.ext hc)
      rw [if_pos hsc, if_pos hc]
    · have hsc : ¬ e.symm ⟨id, hid⟩ = c := fun h => hc (congrArg Subtype.val (e.symm_apply_eq.mp h))
      rw [if_neg hsc, if_neg hc]
  · have hne : id ≠ (e c : String) := fun h => hid (h ▸ (e c).2)
    simp only [dif_neg hid, if_neg hne, mul_zero, add_zero]

/-- **The production Jacobian entry's sign matches the interaction-graph edge sign.** At a strictly
positive state and under `hmono`, the entry `jacobianMatrix E r c` — the `c`-directional derivative of
the `r`-coordinate of the assembled production — carries the sign of the graph edge from `e c` to `e r`:
nonnegative for an activating edge (`+1`), nonpositive for a repressing edge (`−1`), and zero for an
absent edge (`0`). Parallel-edge consistency (`hconsist`) pins the shared sign of every edge between the
pair, and `hmono` excludes non-monotone ports; weak inequalities absorb vanishing summands. -/
private theorem jacobianMatrix_entry_signMatches (g : GRN) (wp : g.WellPosed)
    (hreg : ∀ op ∈ g.operators, op.Regular) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ)
    (hE : HasFDerivAt (g.assembledProd wp e) E z) (hz : ∀ k, 0 < z k)
    (hmono : ∀ edge ∈ signedInteractionGraph g, edge.2.2 = 1 ∨ edge.2.2 = -1)
    (hconsist : EdgeSignConsistent g) (r c : Fin n) :
    (0 < graphEdgeSign g (e c) (e r) → 0 ≤ jacobianMatrix E r c) ∧
      (graphEdgeSign g (e c) (e r) < 0 → jacobianMatrix E r c ≤ 0) ∧
      (graphEdgeSign g (e c) (e r) = 0 → jacobianMatrix E r c = 0) := by
  classical
  obtain ⟨d, hd, hEval⟩ := assembledProd_hasDerivAt_dir g wp hreg e z hz r c
  rw [hEval E hE]
  set c' : String := (e c : String) with hc'
  set Vt : ℝ → String → ℝ :=
    fun t => g.valuation wp.inducer (fun j => (z + t • Pi.single c (1 : ℝ) : Fin n → ℝ) (e.symm j))
      with hVtdef
  set opsr : List Node :=
    g.operators.filter (fun op => decide ((e r : String) ∈ g.outputsOf op.id)) with hopsrdef
  have hf : (fun t : ℝ => g.assembledProd wp e (z + t • Pi.single c (1 : ℝ)) r)
      = fun t => (opsr.map (fun op => g.opRate (Vt t) op)).sum := by
    funext t
    simp only [hVtdef, hopsrdef, GRN.assembledProd, GRN.prodOf]
  rw [hf] at hd
  -- valuation facts under the `c`-axis perturbation
  have hstep : ∀ (t : ℝ) (id : String), Vt t id = Vt 0 id + t * (if id = c' then 1 else 0) := by
    intro t id
    have h1 := ent_valuation_perturb g wp.inducer e z c t id
    have h0 := ent_valuation_perturb g wp.inducer e z c 0 id
    simp only [hVtdef, hc']
    rw [h1, h0]; simp
  have hV0nn : ∀ id, 0 ≤ Vt 0 id := by
    intro id
    have : Vt 0 id = g.valuation wp.inducer (fun j => z (e.symm j)) id := by
      simp only [hVtdef]; rw [ent_valuation_perturb g wp.inducer e z c 0 id]; simp
    rw [this]
    exact g.valuation_nonneg wp.inducer_nonneg (fun k => (hz (e.symm k)).le) id
  have hVge : ∀ (t : ℝ), 0 ≤ t → ∀ id, Vt 0 id ≤ Vt t id := by
    intro t ht id
    rw [hstep t id]
    have hnn : 0 ≤ t * (if id = c' then 1 else 0) := by
      apply mul_nonneg ht; split <;> norm_num
    linarith
  have hVtnn : ∀ (t : ℝ), 0 ≤ t → ∀ id, 0 ≤ Vt t id :=
    fun t ht id => le_trans (hV0nn id) (hVge t ht id)
  have hsame : ∀ (t : ℝ) (id : String), id ≠ c' → Vt t id = Vt 0 id := by
    intro t id hne; rw [hstep t id, if_neg hne]; ring
  -- an operator's rate is unchanged when the perturbation fixes all of its inputs
  have hopEq : ∀ (op : Node) (t : ℝ), (∀ id ∈ g.inputsOf op.id, Vt t id = Vt 0 id) →
      g.opRate (Vt t) op = g.opRate (Vt 0) op := by
    intro op t hids
    unfold GRN.opRate
    exact congrArg (opRateV op) (List.map_congr_left hids)
  -- a `c'`-input port carrying a monotone sign records that sign as the interaction-graph edge sign
  have hportEdge : ∀ (op : Node), op ∈ opsr → ∀ (p : ℕ) (s : Int),
      (g.opEdgeSigns op)[p]? = some (some s) → (g.inputsOf op.id)[p]? = some c' →
      graphEdgeSign g c' (e r : String) = s := by
    intro op hop p s hsp hip
    have hopmem : op ∈ g.operators := List.mem_of_mem_filter hop
    have hout : (e r : String) ∈ g.outputsOf op.id := by
      have := List.of_mem_filter hop; simpa using this
    have hED := ent_edgesFrom_mem (g.opEdgeSigns op) (g.inputsOf op.id) (g.outputsOf op.id)
      p s c' (e r) hsp hip hout
    have hgraph := ent_mem_signedInteractionGraph g op _ hopmem hED
    exact ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s hgraph
  -- the per-operator trichotomy: the rate follows the interaction-graph edge sign along the perturbation
  have hstepOp : ∀ op ∈ opsr, ∀ t, 0 ≤ t →
      (graphEdgeSign g c' (e r : String) = 1 → g.opRate (Vt 0) op ≤ g.opRate (Vt t) op) ∧
      (graphEdgeSign g c' (e r : String) = -1 → g.opRate (Vt t) op ≤ g.opRate (Vt 0) op) ∧
      (graphEdgeSign g c' (e r : String) = 0 → g.opRate (Vt t) op = g.opRate (Vt 0) op) := by
    intro op hop t ht
    have hopmem : op ∈ g.operators := List.mem_of_mem_filter hop
    have hregop : op.Regular := hreg op hopmem
    -- receiver / hill1 share their kinetics and per-port sign
    have hReceiverLike : op.kind = .receiver ∨ op.kind = .hill1 →
        (graphEdgeSign g c' (e r : String) = 1 → g.opRate (Vt 0) op ≤ g.opRate (Vt t) op) ∧
        (graphEdgeSign g c' (e r : String) = -1 → g.opRate (Vt t) op ≤ g.opRate (Vt 0) op) ∧
        (graphEdgeSign g c' (e r : String) = 0 → g.opRate (Vt t) op = g.opRate (Vt 0) op) := by
      intro hkr
      have hK : 0 < op.rparam "K" 1 := by
        rcases hkr with h | h <;>
          (have hh := hregop; simp only [Node.Regular, h] at hh; exact hh.1)
      have hn : 0 ≤ op.rparam "n" 2 := by
        rcases hkr with h | h <;>
          (have hh := hregop; simp only [Node.Regular, h] at hh; exact hh.2)
      have hlen : 2 ≤ op.alphaNums.length := (wp.alpha_wf op hopmem).1 hkr
      set A0 := (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 with hA0def
      set A1 := (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 with hA1def
      have hrate : ∀ s : ℝ, g.opRate (Vt s) op
          = hill A0 A1 (op.rparam "K" 1) (op.rparam "n" 2)
              (((g.inputsOf op.id).map (Vt s)).headD 0) := by
        intro s; rcases hkr with h | h <;>
          simp only [GRN.opRate, opRateV, h, ← hA0def, ← hA1def]
      rcases hidcase : g.inputsOf op.id with _ | ⟨i0, rest⟩
      · have heqop : g.opRate (Vt t) op = g.opRate (Vt 0) op := hopEq op t (by rw [hidcase]; simp)
        exact ⟨fun _ => le_of_eq heqop.symm, fun _ => le_of_eq heqop, fun _ => heqop⟩
      · have hu0 : g.opRate (Vt 0) op
            = hill A0 A1 (op.rparam "K" 1) (op.rparam "n" 2) (Vt 0 i0) := by
          rw [hrate 0, hidcase]; simp
        have hut : g.opRate (Vt t) op
            = hill A0 A1 (op.rparam "K" 1) (op.rparam "n" 2) (Vt t i0) := by
          rw [hrate t, hidcase]; simp
        by_cases hi0 : i0 = c'
        · have hle : Vt 0 i0 ≤ Vt t i0 := hVge t ht i0
          have hmem0 : Vt 0 i0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (hV0nn i0)
          have hmemt : Vt t i0 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (hVtnn t ht i0)
          obtain ⟨q0, q1, qs, hq⟩ : ∃ q0 q1 qs, op.alphaNums = q0 :: q1 :: qs := by
            rcases hh : op.alphaNums with _ | ⟨q0, tl⟩
            · rw [hh] at hlen; simp at hlen
            · rcases tl with _ | ⟨q1, qs⟩
              · rw [hh] at hlen; simp at hlen
              · exact ⟨q0, q1, qs, rfl⟩
          have hA0 : A0 = (q0 : ℝ) := by rw [hA0def, hq]; simp
          have hA1 : A1 = (q1 : ℝ) := by rw [hA1def, hq]; simp
          have hsig : (g.opEdgeSigns op)[0]? = some (pairSign q0 q1) := by
            rcases hkr with h | h <;> simp [GRN.opEdgeSigns, operatorInputSigns, h, hq]
          have hip : (g.inputsOf op.id)[0]? = some c' := by simp [hidcase, hi0]
          rcases lt_trichotomy q0 q1 with hlt | heq | hgt
          · have hps : pairSign q0 q1 = some 1 := by rw [pairSign, if_pos hlt]
            have hge : graphEdgeSign g c' (e r : String) = 1 :=
              hportEdge op hop 0 1 (by rw [hsig, hps]) hip
            have hA : A0 ≤ A1 := by rw [hA0, hA1]; exact_mod_cast hlt.le
            refine ⟨fun _ => ?_, fun hm => ?_, fun h0 => ?_⟩
            · rw [hu0, hut]; exact hill_monotoneOn hK hn hA hmem0 hmemt hle
            · rw [hge] at hm; norm_num at hm
            · rw [hge] at h0; norm_num at h0
          · have hA : A0 = A1 := by rw [hA0, hA1]; exact_mod_cast heq
            refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
              simp only [hu0, hut, hill_flat hK (hV0nn i0) hA, hill_flat hK (hVtnn t ht i0) hA,
                le_refl]
          · have hps : pairSign q0 q1 = some (-1) := by
              rw [pairSign, if_neg (not_lt.mpr hgt.le), if_pos hgt]
            have hge : graphEdgeSign g c' (e r : String) = -1 :=
              hportEdge op hop 0 (-1) (by rw [hsig, hps]) hip
            have hA : A1 ≤ A0 := by rw [hA0, hA1]; exact_mod_cast hgt.le
            refine ⟨fun h1 => ?_, fun _ => ?_, fun h0 => ?_⟩
            · rw [hge] at h1; norm_num at h1
            · rw [hu0, hut]; exact hill_antitoneOn hK hn hA hmem0 hmemt hle
            · rw [hge] at h0; norm_num at h0
        · have heqop : g.opRate (Vt t) op = g.opRate (Vt 0) op := by
            rw [hu0, hut, hsame t i0 hi0]
          exact ⟨fun _ => le_of_eq heqop.symm, fun _ => le_of_eq heqop, fun _ => heqop⟩
    -- dispatch on the operator kind
    rcases hk : op.kind with _ | _ | _ | _ | _ | _ | _ | _
    · exact absurd (List.of_mem_filter hopmem) (by simp [NodeKind.isOperator, hk])
    · exact absurd (List.of_mem_filter hopmem) (by simp [NodeKind.isOperator, hk])
    · exact absurd (List.of_mem_filter hopmem) (by simp [NodeKind.isOperator, hk])
    · refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> simp [GRN.opRate, opRateV, hk]
    · exact hReceiverLike (Or.inl hk)
    · exact hReceiverLike (Or.inr hk)
    · -- hill2
      have hreg2 := hregop
      simp only [Node.Regular, hk] at hreg2
      obtain ⟨hK1, hK2, hN1, hN2⟩ := hreg2
      have hlen : 4 ≤ op.alphaNums.length := (wp.alpha_wf op hopmem).2 hk
      obtain ⟨q0, q1, q2, q3, qs, hq⟩ :
          ∃ q0 q1 q2 q3 qs, op.alphaNums = q0 :: q1 :: q2 :: q3 :: qs := by
        rcases hh : op.alphaNums with _ | ⟨q0, t1⟩
        · rw [hh] at hlen; simp at hlen
        · rcases t1 with _ | ⟨q1, t2⟩
          · rw [hh] at hlen; simp at hlen
          · rcases t2 with _ | ⟨q2, t3⟩
            · rw [hh] at hlen; simp at hlen
            · rcases t3 with _ | ⟨q3, qs⟩
              · rw [hh] at hlen; simp at hlen
              · exact ⟨q0, q1, q2, q3, qs, rfl⟩
      set A0 := (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0 with hA0def
      set A1 := (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 with hA1def
      set A2 := (op.alphaNums.map (fun q => (q : ℝ))).getD 2 0 with hA2def
      set A3 := (op.alphaNums.map (fun q => (q : ℝ))).getD 3 0 with hA3def
      set K1 := (op.rlist "K").getD 0 1 with hK1def
      set K2 := (op.rlist "K").getD 1 1 with hK2def
      set N1 := (op.rlist "n").getD 0 2 with hN1def
      set N2 := (op.rlist "n").getD 1 2 with hN2def
      set u10 := ((g.inputsOf op.id).map (Vt 0)).getD 0 0 with hu10
      set u1t := ((g.inputsOf op.id).map (Vt t)).getD 0 0 with hu1t
      set u20 := ((g.inputsOf op.id).map (Vt 0)).getD 1 0 with hu20
      set u2t := ((g.inputsOf op.id).map (Vt t)).getD 1 0 with hu2t
      have hu0 : g.opRate (Vt 0) op = hill2 A0 A1 A2 A3 K1 K2 N1 N2 u10 u20 := by
        simp only [GRN.opRate, opRateV, hk, ← hA0def, ← hA1def, ← hA2def, ← hA3def,
          ← hK1def, ← hK2def, ← hN1def, ← hN2def, ← hu10, ← hu20]
      have hut : g.opRate (Vt t) op = hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u2t := by
        simp only [GRN.opRate, opRateV, hk, ← hA0def, ← hA1def, ← hA2def, ← hA3def,
          ← hK1def, ← hK2def, ← hN1def, ← hN2def, ← hu1t, ← hu2t]
      have hA0 : A0 = (q0 : ℝ) := by rw [hA0def, hq]; simp
      have hA1 : A1 = (q1 : ℝ) := by rw [hA1def, hq]; simp
      have hA2 : A2 = (q2 : ℝ) := by rw [hA2def, hq]; simp
      have hA3 : A3 = (q3 : ℝ) := by rw [hA3def, hq]; simp
      have hsig0 : (g.opEdgeSigns op)[0]? = some (signFromPairs [(q0, q1), (q2, q3)]) := by
        simp [GRN.opEdgeSigns, operatorInputSigns, hk, hq]
      have hsig1 : (g.opEdgeSigns op)[1]? = some (signFromPairs [(q0, q2), (q1, q3)]) := by
        simp [GRN.opEdgeSigns, operatorInputSigns, hk, hq]
      have hout : (e r : String) ∈ g.outputsOf op.id := by
        have := List.of_mem_filter hop; simpa using this
      have hu1le : u10 ≤ u1t := by
        rw [hu10, hu1t]; exact getD_map_mono (fun id _ => hVge t ht id) 0
      have hu2le : u20 ≤ u2t := by
        rw [hu20, hu2t]; exact getD_map_mono (fun id _ => hVge t ht id) 1
      have hu10n : 0 ≤ u10 := by rw [hu10]; exact getD_map_nonneg' (fun id _ => hV0nn id) 0
      have hu1tn : 0 ≤ u1t := by rw [hu1t]; exact getD_map_nonneg' (fun id _ => hVtnn t ht id) 0
      have hu20n : 0 ≤ u20 := by rw [hu20]; exact getD_map_nonneg' (fun id _ => hV0nn id) 1
      have hu2tn : 0 ≤ u2t := by rw [hu2t]; exact getD_map_nonneg' (fun id _ => hVtnn t ht id) 1
      -- a port that is not `c'` keeps its input fixed under the perturbation
      have hportConst : ∀ k, (g.inputsOf op.id)[k]? ≠ some c' →
          ((g.inputsOf op.id).map (Vt 0)).getD k 0 = ((g.inputsOf op.id).map (Vt t)).getD k 0 := by
        intro k hk'
        rcases hgk : (g.inputsOf op.id)[k]? with _ | x
        · simp [List.getD_eq_getElem?_getD, List.getElem?_map, hgk]
        · have hxne : x ≠ c' := fun hx => hk' (hgk.trans (by rw [hx]))
          simp [List.getD_eq_getElem?_getD, List.getElem?_map, hgk, hsame t x hxne]
      -- the mem-membership witnesses for the interaction edge from a `c'` port
      have hedge0 : (g.inputsOf op.id)[0]? = some c' → ∀ s0,
          signFromPairs [(q0, q1), (q2, q3)] = some s0 →
          (c', (e r : String), s0) ∈ signedInteractionGraph g := by
        intro hp0 s0 hs0
        exact ent_mem_signedInteractionGraph g op _ hopmem
          (ent_edgesFrom_mem _ _ _ 0 s0 c' (e r) (by rw [hsig0, hs0]) hp0 hout)
      have hedge1 : (g.inputsOf op.id)[1]? = some c' → ∀ s1,
          signFromPairs [(q0, q2), (q1, q3)] = some s1 →
          (c', (e r : String), s1) ∈ signedInteractionGraph g := by
        intro hp1 s1 hs1
        exact ent_mem_signedInteractionGraph g op _ hopmem
          (ent_edgesFrom_mem _ _ _ 1 s1 c' (e r) (by rw [hsig1, hs1]) hp1 hout)
      have hmem0 : u10 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hu10n
      have hmemt0 : u1t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hu1tn
      have hmem1 : u20 ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hu20n
      have hmemt1 : u2t ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hu2tn
      refine ⟨fun h1 => ?_, fun hm1 => ?_, fun h0 => ?_⟩
      · -- activating edge: the rate is nondecreasing in both `c'` ports
        have stepL : hill2 A0 A1 A2 A3 K1 K2 N1 N2 u10 u20
            ≤ hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u20 := by
          by_cases hp0 : (g.inputsOf op.id)[0]? = some c'
          · have hpair : A0 ≤ A1 ∧ A2 ≤ A3 := by
              rcases hs0 : signFromPairs [(q0, q1), (q2, q3)] with _ | s0
              · exact ⟨by rw [hA0, hA1]; exact_mod_cast le_of_eq (signFromPairs_none hs0 (q0, q1) (by simp)),
                  by rw [hA2, hA3]; exact_mod_cast le_of_eq (signFromPairs_none hs0 (q2, q3) (by simp))⟩
              · have hge := ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s0 (hedge0 hp0 s0 hs0)
                have : s0 = 1 := hge.symm.trans h1
                subst this
                exact ⟨by rw [hA0, hA1]; exact_mod_cast signFromPairs_one hs0 (q0, q1) (by simp),
                  by rw [hA2, hA3]; exact_mod_cast signFromPairs_one hs0 (q2, q3) (by simp)⟩
            exact hill2_monotoneOn_left hK1 hK2 hN1 hu20n hpair.1 hpair.2 hmem0 hmemt0 hu1le
          · exact le_of_eq (by rw [hu10, hu1t]; rw [hportConst 0 hp0])
        have stepR : hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u20
            ≤ hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u2t := by
          by_cases hp1 : (g.inputsOf op.id)[1]? = some c'
          · have hpair : A0 ≤ A2 ∧ A1 ≤ A3 := by
              rcases hs1 : signFromPairs [(q0, q2), (q1, q3)] with _ | s1
              · exact ⟨by rw [hA0, hA2]; exact_mod_cast le_of_eq (signFromPairs_none hs1 (q0, q2) (by simp)),
                  by rw [hA1, hA3]; exact_mod_cast le_of_eq (signFromPairs_none hs1 (q1, q3) (by simp))⟩
              · have hge := ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s1 (hedge1 hp1 s1 hs1)
                have : s1 = 1 := hge.symm.trans h1
                subst this
                exact ⟨by rw [hA0, hA2]; exact_mod_cast signFromPairs_one hs1 (q0, q2) (by simp),
                  by rw [hA1, hA3]; exact_mod_cast signFromPairs_one hs1 (q1, q3) (by simp)⟩
            exact hill2_monotoneOn_right hK1 hK2 hN2 hu1tn hpair.1 hpair.2 hmem1 hmemt1 hu2le
          · exact le_of_eq (by rw [hu20, hu2t]; rw [hportConst 1 hp1])
        rw [hu0, hut]; exact le_trans stepL stepR
      · -- repressing edge: the rate is nonincreasing in both `c'` ports
        have stepL : hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u20
            ≤ hill2 A0 A1 A2 A3 K1 K2 N1 N2 u10 u20 := by
          by_cases hp0 : (g.inputsOf op.id)[0]? = some c'
          · have hpair : A1 ≤ A0 ∧ A3 ≤ A2 := by
              rcases hs0 : signFromPairs [(q0, q1), (q2, q3)] with _ | s0
              · exact ⟨by rw [hA0, hA1]; exact_mod_cast le_of_eq (signFromPairs_none hs0 (q0, q1) (by simp)).symm,
                  by rw [hA2, hA3]; exact_mod_cast le_of_eq (signFromPairs_none hs0 (q2, q3) (by simp)).symm⟩
              · have hge := ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s0 (hedge0 hp0 s0 hs0)
                have : s0 = -1 := hge.symm.trans hm1
                subst this
                exact ⟨by rw [hA0, hA1]; exact_mod_cast signFromPairs_neg hs0 (q0, q1) (by simp),
                  by rw [hA2, hA3]; exact_mod_cast signFromPairs_neg hs0 (q2, q3) (by simp)⟩
            exact hill2_antitoneOn_left hK1 hK2 hN1 hu20n hpair.1 hpair.2 hmem0 hmemt0 hu1le
          · exact le_of_eq (by rw [hu10, hu1t]; rw [hportConst 0 hp0])
        have stepR : hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u2t
            ≤ hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u20 := by
          by_cases hp1 : (g.inputsOf op.id)[1]? = some c'
          · have hpair : A2 ≤ A0 ∧ A3 ≤ A1 := by
              rcases hs1 : signFromPairs [(q0, q2), (q1, q3)] with _ | s1
              · exact ⟨by rw [hA0, hA2]; exact_mod_cast le_of_eq (signFromPairs_none hs1 (q0, q2) (by simp)).symm,
                  by rw [hA1, hA3]; exact_mod_cast le_of_eq (signFromPairs_none hs1 (q1, q3) (by simp)).symm⟩
              · have hge := ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s1 (hedge1 hp1 s1 hs1)
                have : s1 = -1 := hge.symm.trans hm1
                subst this
                exact ⟨by rw [hA0, hA2]; exact_mod_cast signFromPairs_neg hs1 (q0, q2) (by simp),
                  by rw [hA1, hA3]; exact_mod_cast signFromPairs_neg hs1 (q1, q3) (by simp)⟩
            exact hill2_antitoneOn_right hK1 hK2 hN2 hu1tn hpair.1 hpair.2 hmem1 hmemt1 hu2le
          · exact le_of_eq (by rw [hu20, hu2t]; rw [hportConst 1 hp1])
        rw [hu0, hut]; exact le_trans stepR stepL
      · -- absent edge: each `c'` port is non-monotone-free, so the rate is flat in it
        have stepL : hill2 A0 A1 A2 A3 K1 K2 N1 N2 u10 u20
            = hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u20 := by
          by_cases hp0 : (g.inputsOf op.id)[0]? = some c'
          · rcases hs0 : signFromPairs [(q0, q1), (q2, q3)] with _ | s0
            · have e01 : A0 = A1 := by rw [hA0, hA1]; exact_mod_cast signFromPairs_none hs0 (q0, q1) (by simp)
              have e23 : A2 = A3 := by rw [hA2, hA3]; exact_mod_cast signFromPairs_none hs0 (q2, q3) (by simp)
              exact le_antisymm
                (hill2_monotoneOn_left hK1 hK2 hN1 hu20n (le_of_eq e01) (le_of_eq e23)
                  hmem0 hmemt0 hu1le)
                (hill2_antitoneOn_left hK1 hK2 hN1 hu20n (le_of_eq e01.symm) (le_of_eq e23.symm)
                  hmem0 hmemt0 hu1le)
            · exfalso
              have hge := ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s0 (hedge0 hp0 s0 hs0)
              have hs00 : s0 = 0 := hge.symm.trans h0
              rcases hmono _ (hedge0 hp0 s0 hs0) with hh | hh <;> rw [hs00] at hh <;> norm_num at hh
          · exact by rw [hu10, hu1t]; rw [hportConst 0 hp0]
        have stepR : hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u20
            = hill2 A0 A1 A2 A3 K1 K2 N1 N2 u1t u2t := by
          by_cases hp1 : (g.inputsOf op.id)[1]? = some c'
          · rcases hs1 : signFromPairs [(q0, q2), (q1, q3)] with _ | s1
            · have e02 : A0 = A2 := by rw [hA0, hA2]; exact_mod_cast signFromPairs_none hs1 (q0, q2) (by simp)
              have e13 : A1 = A3 := by rw [hA1, hA3]; exact_mod_cast signFromPairs_none hs1 (q1, q3) (by simp)
              exact le_antisymm
                (hill2_monotoneOn_right hK1 hK2 hN2 hu1tn (le_of_eq e02) (le_of_eq e13)
                  hmem1 hmemt1 hu2le)
                (hill2_antitoneOn_right hK1 hK2 hN2 hu1tn (le_of_eq e02.symm) (le_of_eq e13.symm)
                  hmem1 hmemt1 hu2le)
            · exfalso
              have hge := ent_graphEdgeSign_eq_of_mem g hconsist c' (e r) s1 (hedge1 hp1 s1 hs1)
              have hs00 : s1 = 0 := hge.symm.trans h0
              rcases hmono _ (hedge1 hp1 s1 hs1) with hh | hh <;> rw [hs00] at hh <;> norm_num at hh
          · exact by rw [hu20, hu2t]; rw [hportConst 1 hp1]
        rw [hu0, hut]; exact (stepL.trans stepR).symm
    · -- sum: every input port activates, so the rate is monotone; a `c'` input forces edge sign `+1`
      have hregsum : ∀ i, 0 < (op.rlist "K").getD i 1 ∧ 0 ≤ (op.rlist "n").getD i 2 := by
        have hh := hregop; simp only [Node.Regular, hk] at hh; exact hh
      have hsumrate : ∀ s : ℝ, g.opRate (Vt s) op
          = ((List.range (((g.inputsOf op.id).map (Vt s)).length)).map (fun i =>
              hill (((op.rnested "alpha").getD i []).getD 0 0)
                (((op.rnested "alpha").getD i []).getD 1 0)
                ((op.rlist "K").getD i 1) ((op.rlist "n").getD i 2)
                (((g.inputsOf op.id).map (Vt s)).getD i 0))).sum := by
        intro s; simp only [GRN.opRate, opRateV, hk]
      have hmonoSum : g.opRate (Vt 0) op ≤ g.opRate (Vt t) op := by
        rw [hsumrate 0, hsumrate t, List.length_map, List.length_map]
        refine List.sum_le_sum (fun i _ => ?_)
        refine hill_monotoneOn (hregsum i).1 (hregsum i).2 (wp.sum_wp op hopmem i).2.2.2
          (Set.mem_Ici.mpr (getD_map_nonneg' (fun id _ => hV0nn id) i))
          (Set.mem_Ici.mpr (getD_map_nonneg' (fun id _ => hVtnn t ht id) i))
          (getD_map_mono (fun id _ => hVge t ht id) i)
      have hIn : c' ∈ g.inputsOf op.id → graphEdgeSign g c' (e r : String) = 1 := by
        intro hcin
        obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hcin
        have hplt : p < (g.inputsOf op.id).length := by
          rw [List.getElem?_eq_some_iff] at hp; exact hp.1
        have hsig : (g.opEdgeSigns op)[p]? = some (some 1) := by
          simp only [GRN.opEdgeSigns, hk, List.getElem?_replicate, if_pos hplt]
        exact hportEdge op hop p 1 hsig hp
      refine ⟨fun _ => hmonoSum, fun hm1 => ?_, fun h0 => ?_⟩
      · have hnotin : c' ∉ g.inputsOf op.id := fun hcin => by rw [hIn hcin] at hm1; norm_num at hm1
        exact le_of_eq (hopEq op t (fun id hid => hsame t id (fun h => hnotin (h ▸ hid))))
      · have hnotin : c' ∉ g.inputsOf op.id := fun hcin => by rw [hIn hcin] at h0; norm_num at h0
        exact hopEq op t (fun id hid => hsame t id (fun h => hnotin (h ▸ hid)))
  have hmonoOp : graphEdgeSign g c' (e r : String) = 1 → ∀ t, 0 ≤ t →
      ∀ op ∈ opsr, g.opRate (Vt 0) op ≤ g.opRate (Vt t) op :=
    fun h t ht op hop => (hstepOp op hop t ht).1 h
  have hantiOp : graphEdgeSign g c' (e r : String) = -1 → ∀ t, 0 ≤ t →
      ∀ op ∈ opsr, g.opRate (Vt t) op ≤ g.opRate (Vt 0) op :=
    fun h t ht op hop => (hstepOp op hop t ht).2.1 h
  have hconstOp : graphEdgeSign g c' (e r : String) = 0 → ∀ t, 0 ≤ t →
      ∀ op ∈ opsr, g.opRate (Vt t) op = g.opRate (Vt 0) op :=
    fun h t ht op hop => (hstepOp op hop t ht).2.2 h
  refine ⟨fun hpos => ?_, fun hneg => ?_, fun hzero => ?_⟩
  · have hs1 : graphEdgeSign g c' (e r : String) = 1 := by
      rcases graphEdgeSign_eq_one_or_neg_one g c' (e r : String) hmono (ne_of_gt hpos) with h | h
      · exact h
      · rw [h] at hpos; norm_num at hpos
    refine ent_deriv_nonneg_of_right hd (fun t ht => ?_)
    exact List.sum_le_sum (hmonoOp hs1 t ht)
  · have hsm1 : graphEdgeSign g c' (e r : String) = -1 := by
      rcases graphEdgeSign_eq_one_or_neg_one g c' (e r : String) hmono (ne_of_lt hneg) with h | h
      · rw [h] at hneg; norm_num at hneg
      · exact h
    refine ent_deriv_nonpos_of_right hd (fun t ht => ?_)
    exact List.sum_le_sum (hantiOp hsm1 t ht)
  · have heqsum : ∀ t, 0 ≤ t →
        (opsr.map (fun op => g.opRate (Vt t) op)).sum
          = (opsr.map (fun op => g.opRate (Vt 0) op)).sum :=
      fun t ht => congrArg List.sum (List.map_congr_left (fun op hop => hconstOp hzero t ht op hop))
    have hge : 0 ≤ d := ent_deriv_nonneg_of_right hd (fun t ht => le_of_eq (heqsum t ht).symm)
    have hle : d ≤ 0 := ent_deriv_nonpos_of_right hd (fun t ht => le_of_eq (heqsum t ht))
    linarith

/-- The negated-field Jacobian is degradation on the diagonal minus the production Jacobian. -/
private theorem negJac_eq_diag_sub (g : GRN) (wp : g.WellPosed) {n : ℕ} (e : Fin n ≃ g.Species)
    (E : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    g.negJac wp e E = Matrix.diagonal (fun k => wp.γ (e k)) - jacobianMatrix E := by
  simp only [GRN.negJac]
  rw [jacobianMatrix_sub, jacobianMatrix_degCLM]

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
    (hconsist : EdgeSignConsistent g)
    (r c : Fin n) (hrc : r ≠ c) :
    (0 < graphEdgeSign g (e c) (e r) → g.negJac wp e E r c ≤ 0) ∧
      (graphEdgeSign g (e c) (e r) < 0 → 0 ≤ g.negJac wp e E r c) ∧
      (graphEdgeSign g (e c) (e r) = 0 → g.negJac wp e E r c = 0) := by
  have hentry : g.negJac wp e E r c = - jacobianMatrix E r c := by
    rw [negJac_eq_diag_sub, Matrix.sub_apply, Matrix.diagonal_apply, if_neg hrc, zero_sub]
  obtain ⟨h1, h2, h3⟩ := jacobianMatrix_entry_signMatches g wp hreg e E z hE hz hmono hconsist r c
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hentry, neg_nonpos]; exact h1 h
  · rw [hentry, neg_nonneg]; exact h2 h
  · rw [hentry, h3 h, neg_zero]

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
    (hconsist : EdgeSignConsistent g)
    (hnopos : hasPositiveLoopEdges (signedInteractionGraph g) = false) :
    ∀ k, 0 < g.negJac wp e E k k := by
  intro k
  have hentry : g.negJac wp e E k k = wp.γ (e k) - jacobianMatrix E k k := by
    rw [negJac_eq_diag_sub, Matrix.sub_apply, Matrix.diagonal_apply_eq]
  obtain ⟨h1, h2, h3⟩ := jacobianMatrix_entry_signMatches g wp hreg e E z hE hz hmono hconsist k k
  have hjle : jacobianMatrix E k k ≤ 0 := by
    rcases lt_trichotomy (graphEdgeSign g (e k) (e k)) 0 with hlt | heq | hgt
    · exact h2 hlt
    · rw [h3 heq]
    · exfalso
      have hne : graphEdgeSign g (e k) (e k) ≠ 0 := ne_of_gt hgt
      have h1eq : graphEdgeSign g (e k) (e k) = 1 := by
        rcases graphEdgeSign_eq_one_or_neg_one g (e k) (e k) hmono hne with h | h
        · exact h
        · rw [h] at hgt; norm_num at hgt
      have hmemc : (1 : Int) ∈ cycleSignsEdges (signedInteractionGraph g) := by
        unfold graphEdgeSign at h1eq
        cases hf : (g.signedInteractionGraph).find?
            (fun ed => ed.1 == (e k : String) && ed.2.1 == (e k : String)) with
        | none => rw [hf] at h1eq; simp at h1eq
        | some ed =>
          rw [hf] at h1eq
          have hmem := List.mem_of_find?_eq_some hf
          have hcond := List.find?_some hf
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨a, b, sgn⟩ := ed
          simp only at hcond h1eq
          obtain ⟨rfl, rfl⟩ := hcond
          subst h1eq
          exact selfEdge_sign_mem_cycleSignsEdges _ _ _ hmem
      have hcontra : hasPositiveLoopEdges (signedInteractionGraph g) = true := by
        unfold hasPositiveLoopEdges
        rw [List.any_eq_true]
        exact ⟨1, hmemc, by decide⟩
      rw [hnopos] at hcontra
      exact Bool.noConfusion hcontra
  rw [hentry]
  linarith [wp.γ_pos (e k)]

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
  intro s hs
  by_contra hns
  rw [not_le] at hns
  have hpos : hasPositiveLoopEdges edges = true := by
    unfold hasPositiveLoopEdges
    rw [List.any_eq_true]
    exact ⟨s, hs, by simpa using hns⟩
  rw [h] at hpos
  exact Bool.noConfusion hpos

/-- If some neighbour either closes the cycle at `start` (contributing `prod * sign`) or opens a fresh
DFS branch containing `val`, then `val` is in the neighbour fold of one DFS step. -/
private theorem foldr_dfs_mem (E : List SignedEdge) (fuel : ℕ) (start : String) (path : List String)
    (prod : Int) (ns : List (String × Int)) (val : Int)
    (hw : ∃ nb ∈ ns, (nb.1 = start ∧ val = prod * nb.2) ∨
          (nb.1 ≠ start ∧ ¬ (path.any (· == nb.1)) ∧
           val ∈ cycleSignsEdges.dfs E fuel start nb.1 (nb.1 :: path) (prod * nb.2))) :
    val ∈ ns.foldr (fun nb acc =>
      if nb.1 == start then (prod * nb.2) :: acc
      else if path.any (· == nb.1) then acc
      else cycleSignsEdges.dfs E fuel start nb.1 (nb.1 :: path) (prod * nb.2) ++ acc) [] := by
  induction ns with
  | nil => simp at hw
  | cons nb0 rest ih =>
    simp only [List.foldr_cons]
    set acc := rest.foldr (fun nb acc =>
      if nb.1 == start then (prod * nb.2) :: acc
      else if path.any (· == nb.1) then acc
      else cycleSignsEdges.dfs E fuel start nb.1 (nb.1 :: path) (prod * nb.2) ++ acc) [] with hacc
    obtain ⟨nb, hnb, hW⟩ := hw
    rcases List.mem_cons.mp hnb with rfl | hrest
    · rcases hW with ⟨hs, hval⟩ | ⟨hns, hnp, hdfs⟩
      · have hcond : (nb.1 == start) = true := by rw [beq_iff_eq]; exact hs
        rw [if_pos hcond, hval]; exact List.mem_cons.mpr (Or.inl rfl)
      · have hcond : ¬ ((nb.1 == start) = true) := by rw [beq_iff_eq]; exact hns
        rw [if_neg hcond, if_neg hnp]; exact List.mem_append_left _ hdfs
    · have hmem_acc : val ∈ acc := ih ⟨nb, hrest, hW⟩
      by_cases hs : (nb0.1 == start) = true
      · rw [if_pos hs]; exact List.mem_cons_of_mem _ hmem_acc
      · rw [if_neg hs]
        by_cases hp : path.any (· == nb0.1) = true
        · rw [if_pos hp]; exact hmem_acc
        · rw [if_neg hp]; exact List.mem_append_right _ hmem_acc

/-- **Product completeness of the DFS.** A simple signed walk `w` (each step a graph edge with its sign,
ending at `start`, its interior vertices distinct and avoiding `path`) contributes `prod` times the
product of its step signs to the DFS from `node`. -/
private theorem dfs_prod_mem (E : List SignedEdge) (start : String) :
    ∀ (w : List (String × Int)) (fuel : ℕ) (node : String) (path : List String) (prod : Int),
    List.IsChain (fun a b : String × Int => (a.1, b.1, b.2) ∈ E) ((node, (0 : Int)) :: w) →
    w ≠ [] → (w.getLast?).map Prod.fst = some start →
    (w.dropLast.map Prod.fst).Nodup → (∀ x ∈ w.dropLast.map Prod.fst, x ∉ path) →
    start ∈ path → w.length ≤ fuel →
    prod * (w.map Prod.snd).prod ∈ cycleSignsEdges.dfs E fuel start node path prod := by
  intro w
  induction w with
  | nil => intro _ _ _ _ _ hne; exact absurd rfl hne
  | cons hd rest ih =>
    intro fuel node path prod hchain _ hlast hnodup hdisj hstart hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := by
      cases fuel with
      | zero => simp at hfuel
      | succ f => exact ⟨f, rfl⟩
    have hedge : (node, hd.1, hd.2) ∈ E := hchain.rel_head
    have hnb : (hd.1, hd.2) ∈ neighbors E node := js_mem_neighbors E node hd.1 hd.2 hedge
    simp only [cycleSignsEdges.dfs]
    refine foldr_dfs_mem E f start path prod (neighbors E node) _ ?_
    refine ⟨(hd.1, hd.2), hnb, ?_⟩
    rcases rest with _ | ⟨hd2, rest2⟩
    · left
      refine ⟨?_, ?_⟩
      · simpa using hlast
      · simp
    · right
      have hd1mem : hd.1 ∈ (hd :: hd2 :: rest2).dropLast.map Prod.fst := by
        rw [List.dropLast_cons_of_ne_nil (by simp), List.map_cons]; exact List.mem_cons.mpr (Or.inl rfl)
      have hd1notpath : hd.1 ∉ path := hdisj hd.1 hd1mem
      refine ⟨fun hcontra => hd1notpath (hcontra ▸ hstart), ?_, ?_⟩
      · simp only [List.any_eq_true, not_exists, not_and]
        intro x hx hxe; rw [beq_iff_eq] at hxe; exact hd1notpath (hxe ▸ hx)
      · -- recurse
        have htail : List.IsChain (fun a b : String × Int => (a.1, b.1, b.2) ∈ E) (hd :: hd2 :: rest2) :=
          hchain.tail
        have hc2 : List.IsChain (fun a b : String × Int => (a.1, b.1, b.2) ∈ E)
            ((hd.1, (0 : Int)) :: hd2 :: rest2) := by
          rw [List.isChain_cons] at htail ⊢; exact ⟨htail.1, htail.2⟩
        have hlast' : ((hd2 :: rest2).getLast?).map Prod.fst = some start := by
          rwa [List.getLast?_cons_cons] at hlast
        have hdl : (hd :: hd2 :: rest2).dropLast = hd :: (hd2 :: rest2).dropLast :=
          List.dropLast_cons_of_ne_nil (by simp)
        rw [hdl, List.map_cons] at hnodup hdisj
        have hnodup' : ((hd2 :: rest2).dropLast.map Prod.fst).Nodup := hnodup.of_cons
        have hdisj' : ∀ x ∈ (hd2 :: rest2).dropLast.map Prod.fst, x ∉ hd.1 :: path := by
          intro x hx
          have hxp : x ∉ path := hdisj x (List.mem_cons_of_mem _ hx)
          have hxne : x ≠ hd.1 := fun h => (List.nodup_cons.mp hnodup).1 (h ▸ hx)
          simp only [List.mem_cons, not_or]; exact ⟨hxne, hxp⟩
        have hfuel' : (hd2 :: rest2).length ≤ f := by
          simp only [List.length_cons] at hfuel ⊢; omega
        have hval_eq : prod * ((hd :: hd2 :: rest2).map Prod.snd).prod
            = (prod * hd.2) * ((hd2 :: rest2).map Prod.snd).prod := by
          rw [List.map_cons, List.prod_cons, mul_assoc]
        rw [hval_eq]
        exact ih f hd.1 (hd.1 :: path) (prod * hd.2) hc2 (by simp) hlast' hnodup' hdisj'
          (List.mem_cons_of_mem _ hstart) hfuel'

-- UNIT: perm-cycle-correspondence  (combinatorial; the new sub-lemma)
/-- **A `Perm`-cycle is a directed graph cycle.** A nontrivial cycle `σ` of `Fin n` whose every step
`e i → e (σ i)` is a signed interaction edge (`graphEdgeSign ≠ 0`) maps to a directed cycle enumerated by
`cycleSignsEdges`: the product of the graph edge signs around `σ`'s orbit occurs in
`cycleSignsEdges (signedInteractionGraph g)`. This is the bridge between the algebraic cover-term
index (`Equiv.Perm`) and the graph-combinatorial cycle enumeration. -/
theorem cycleSign_mem_cycleSignsEdges (g : GRN) {n : ℕ} (e : Fin n ≃ g.Species)
    (hconsist : EdgeSignConsistent g)
    (σ : Equiv.Perm (Fin n)) (hσ : σ.IsCycle)
    (hstep : ∀ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) ≠ 0) :
    (∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i))) ∈
      cycleSignsEdges (signedInteractionGraph g) := by
  classical
  set E := signedInteractionGraph g with hEdef
  have hσ2 := hσ
  obtain ⟨x₀, hx₀ne, -⟩ := hσ2
  have hx₀mem : x₀ ∈ σ.support := Equiv.Perm.mem_support.mpr hx₀ne
  have hsc : ∀ {y}, σ.SameCycle x₀ y ↔ σ y ≠ y := (Equiv.Perm.isCycle_iff_sameCycle hx₀ne).mp hσ
  have hLnodup : (σ.toList x₀).Nodup := Equiv.Perm.nodup_toList σ x₀
  have hcyc : σ.cycleOf x₀ = σ := hσ.cycleOf_eq hx₀ne
  have hLlen : (σ.toList x₀).length = σ.support.card := by rw [Equiv.Perm.length_toList, hcyc]
  have hLne : σ.toList x₀ ≠ [] := by
    rw [Ne, Equiv.Perm.toList_eq_nil_iff]; exact fun h => h hx₀mem
  have hLmem : ∀ y, y ∈ σ.toList x₀ ↔ y ∈ σ.support := by
    intro y
    rw [Equiv.Perm.mem_toList_iff]
    constructor
    · rintro ⟨h, _⟩; exact Equiv.Perm.mem_support.mpr (hsc.mp h)
    · intro h; exact ⟨hsc.mpr (Equiv.Perm.mem_support.mp h), hx₀mem⟩
  have htoFinset : (σ.toList x₀).toFinset = σ.support := by ext y; rw [List.mem_toFinset, hLmem]
  have hLget : ∀ (k : ℕ) (hk : k < (σ.toList x₀).length), (σ.toList x₀)[k] = (σ ^ k) x₀ :=
    fun k hk => Equiv.Perm.getElem_toList σ x₀ k hk
  have hLhead : (σ.toList x₀).head? = some x₀ := by
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (List.length_pos_iff.mpr hLne),
      Equiv.Perm.toList_getElem_zero σ x₀ hx₀mem]
  have hcardpos : 0 < σ.support.card := Finset.card_pos.mpr ⟨x₀, hx₀mem⟩
  have hord : (σ ^ σ.support.card) x₀ = x₀ := by
    have h1 : σ ^ σ.support.card = 1 := by rw [← hσ.orderOf]; exact pow_orderOf_eq_one σ
    rw [h1, Equiv.Perm.one_apply]
  have hedge : ∀ i, i ∈ σ.support →
      ((e i : String), (e (σ i) : String), graphEdgeSign g (e i) (e (σ i))) ∈ E := by
    intro i hi
    have hne := hstep i hi
    unfold graphEdgeSign at hne ⊢
    rcases hf : (g.signedInteractionGraph).find?
        (fun ed => ed.1 == (e i : String) && ed.2.1 == (e (σ i) : String)) with _ | ed
    · rw [hf] at hne; simp at hne
    · rw [hf]
      have hmem := List.mem_of_find?_eq_some hf
      have hcond := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨a, b, s⟩ := ed
      simp only at hcond ⊢
      obtain ⟨rfl, rfl⟩ := hcond
      exact hEdef ▸ hmem
  set start : String := (e x₀ : String) with hstartdef
  set F : Fin n → String × Int :=
    fun i => ((e (σ i) : String), graphEdgeSign g (e i) (e (σ i))) with hFdef
  set w : List (String × Int) := (σ.toList x₀).map F with hwdef
  have hinj : Function.Injective (fun i : Fin n => (e (σ i) : String)) :=
    fun a b hab => σ.injective (e.injective (Subtype.coe_injective hab))
  have hwfst : w.map Prod.fst = (σ.toList x₀).map (fun i => (e (σ i) : String)) := by
    rw [hwdef, List.map_map]; rfl
  have hwfstnodup : (w.map Prod.fst).Nodup := by rw [hwfst]; exact hLnodup.map hinj
  have hwne : w ≠ [] := by rw [hwdef]; exact fun h => hLne (List.map_eq_nil_iff.mp h)
  have hsnd : w.map Prod.snd = (σ.toList x₀).map (fun i => graphEdgeSign g (e i) (e (σ i))) := by
    rw [hwdef, List.map_map]; rfl
  have hprodeq : (∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i))) = (w.map Prod.snd).prod := by
    rw [hsnd, ← htoFinset, List.prod_toFinset _ hLnodup]
  have hσnx : σ ((σ ^ ((σ.toList x₀).length - 1)) x₀) = x₀ := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ', hLlen, Nat.sub_add_cancel hcardpos]; exact hord
  have hwlast : (w.getLast?).map Prod.fst = some start := by
    rw [hwdef, List.getLast?_map, Option.map_map, List.getLast?_eq_getElem?]
    have hidx : (σ.toList x₀).length - 1 < (σ.toList x₀).length :=
      Nat.sub_lt (List.length_pos_iff.mpr hLne) one_pos
    rw [List.getElem?_eq_getElem hidx, Option.map_some]
    show some (e (σ ((σ.toList x₀)[(σ.toList x₀).length - 1])) : String) = some start
    rw [hLget _ hidx, hσnx, hstartdef]
  have hstart_last : (w.map Prod.fst).getLast? = some start := by
    rw [List.getLast?_map]; exact hwlast
  have hwne_fst : w.map Prod.fst ≠ [] := fun h => hwne (List.map_eq_nil_iff.mp h)
  have hgetlast : (w.map Prod.fst).getLast hwne_fst = start := by
    have h1 := List.getLast?_eq_getLast_of_ne_nil hwne_fst
    rw [hstart_last] at h1; exact (Option.some_inj.mp h1).symm
  have hwnodup : (w.dropLast.map Prod.fst).Nodup := by
    rw [List.map_dropLast]; exact (List.dropLast_sublist _).nodup hwfstnodup
  have hwdisj : ∀ x ∈ w.dropLast.map Prod.fst, x ∉ ([start] : List String) := by
    rw [List.map_dropLast]
    intro x hx hxs
    simp only [List.mem_singleton] at hxs; subst hxs
    have hsplit := List.dropLast_concat_getLast hwne_fst
    have hnd : (w.map Prod.fst).Nodup := hwfstnodup
    rw [← hsplit, List.nodup_append] at hnd
    rw [hgetlast] at hnd
    exact hnd.2.2 start hx start (List.mem_singleton.mpr rfl) rfl
  have hsub : (w.map Prod.fst) ⊆ verticesOf E := by
    intro x hx
    rw [hwfst, List.mem_map] at hx
    obtain ⟨i, hiL, rfl⟩ := hx
    have hisupp : i ∈ σ.support := (hLmem i).mp hiL
    have hσisupp : σ i ∈ σ.support := Equiv.Perm.apply_mem_support.mpr hisupp
    rw [js_verticesOf_mem]; exact ⟨_, hedge (σ i) hσisupp, Or.inl rfl⟩
  have hwfuel : w.length ≤ (verticesOf E).length + 1 := by
    have h1 : (w.map Prod.fst).length ≤ (verticesOf E).length :=
      (List.subperm_of_subset hwfstnodup hsub).length_le
    rw [List.length_map] at h1; omega
  have hSchain : List.IsChain
      (fun a b : Fin n =>
        ((e (σ a) : String), (e (σ b) : String), graphEdgeSign g (e b) (e (σ b))) ∈ E)
      (σ.toList x₀) := by
    rw [List.isChain_iff_getElem]
    intro k hk
    have hk1 : k < (σ.toList x₀).length := Nat.lt_of_succ_lt hk
    have hsucc : (σ.toList x₀)[k + 1] = σ ((σ.toList x₀)[k]) := by
      rw [hLget (k + 1) hk, hLget k hk1, pow_succ', Equiv.Perm.mul_apply]
    have hmemk1 : (σ.toList x₀)[k + 1] ∈ σ.support := (hLmem _).mp (List.getElem_mem hk)
    have hh := hedge (σ.toList x₀)[k + 1] hmemk1
    rw [← hsucc]; exact hh
  have hwchain : List.IsChain (fun a b : String × Int => (a.1, b.1, b.2) ∈ E)
      ((start, (0 : Int)) :: w) := by
    rw [List.isChain_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [hwdef, List.head?_map, hLhead, Option.map_some] at hy
      rw [Option.mem_some_iff] at hy; subst hy
      exact hedge x₀ hx₀mem
    · rw [hwdef]; exact (List.isChain_map F).2 hSchain
  have hmain : (w.map Prod.snd).prod ∈
      cycleSignsEdges.dfs E ((verticesOf E).length + 1) start start [start] 1 := by
    have hh := dfs_prod_mem E start w ((verticesOf E).length + 1) start [start] 1
      hwchain hwne hwlast hwnodup hwdisj (List.mem_singleton.mpr rfl) hwfuel
    simpa using hh
  have hstartmem : start ∈ verticesOf E := by
    rw [js_verticesOf_mem]; exact ⟨_, hedge x₀ hx₀mem, Or.inl rfl⟩
  rw [hprodeq, cycleSignsEdges]
  refine js_mem_foldr_of_step _ ?_ [] (verticesOf E) start hstartmem ((w.map Prod.snd).prod) ?_
  · intro v acc x hx; exact List.mem_append_right _ hx
  · intro acc; exact List.mem_append_left _ hmain

/-- **Support-restricted cover factorisation.** The cover term of `π` splits into the sign times the
diagonal-entry product over `π`'s support (the "moved" points), times the plain diagonal product over
the fixed points. The support-restricted factor is multiplicative over disjoint permutations, whereas
`coverTerm` itself is not; the fixed-point factor is a product of positive diagonal entries. -/
private theorem coverTerm_eq_supportCover {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (π : Equiv.Perm (Fin n)) :
    coverTerm M π =
      (((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ i ∈ π.support, M (π i) i) *
        ∏ i ∈ (π.support)ᶜ, M i i := by
  have hcoe : coverTerm M π = ((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ i, M (π i) i := by
    unfold coverTerm
    rw [coverCoeff_eq_sign]
  rw [hcoe, mul_assoc]
  congr 1
  have hc : (∏ i ∈ (π.support)ᶜ, M i i) = ∏ i ∈ (π.support)ᶜ, M (π i) i := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hi
    rw [hi]
  rw [hc, Finset.prod_mul_prod_compl]

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
  -- The support-restricted cover factor is nonnegative for every permutation: it is `1` on the
  -- identity, agrees in sign with `coverTerm` on a single cycle, and is multiplicative over the
  -- disjoint-cycle factorisation.
  have main : ∀ π : Equiv.Perm (Fin n),
      0 ≤ ((Equiv.Perm.sign π : ℤ) : ℝ) * ∏ i ∈ π.support, M (π i) i := by
    intro π
    induction π using Equiv.Perm.cycle_induction_on with
    | base_one =>
        rw [Equiv.Perm.support_one, Finset.prod_empty, mul_one, Equiv.Perm.sign_one,
          Units.val_one, Int.cast_one]
        exact zero_le_one
    | base_cycles σ hσ =>
        have hpos : 0 < ∏ i ∈ (σ.support)ᶜ, M i i := Finset.prod_pos (fun i _ => hdiag i)
        have hct := hcyc σ hσ
        rw [coverTerm_eq_supportCover] at hct
        exact nonneg_of_mul_nonneg_left hct hpos
    | induction_disjoint σ τ hd _ hPσ hPτ =>
        have e1 : ∀ i ∈ σ.support, M ((σ * τ) i) i = M (σ i) i := by
          intro i hi
          have hτ : τ i = i := (hd i).resolve_left (Equiv.Perm.mem_support.mp hi)
          rw [Equiv.Perm.mul_apply, hτ]
        have e2 : ∀ i ∈ τ.support, M ((σ * τ) i) i = M (τ i) i := by
          intro i hi
          have hτi : τ i ∈ τ.support := Equiv.Perm.apply_mem_support.mpr hi
          have hσfix : σ (τ i) = τ i := (hd (τ i)).resolve_right (Equiv.Perm.mem_support.mp hτi)
          rw [Equiv.Perm.mul_apply, hσfix]
        calc (0 : ℝ)
            ≤ (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i ∈ σ.support, M (σ i) i) *
                (((Equiv.Perm.sign τ : ℤ) : ℝ) * ∏ i ∈ τ.support, M (τ i) i) :=
              mul_nonneg hPσ hPτ
          _ = ((Equiv.Perm.sign (σ * τ) : ℤ) : ℝ) * ∏ i ∈ (σ * τ).support, M ((σ * τ) i) i := by
              rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, hd.support_mul,
                Finset.prod_union hd.disjoint_support, Finset.prod_congr rfl e1,
                Finset.prod_congr rfl e2]
              ring
  refine ⟨fun π => ?_, ?_⟩
  · have hpos : 0 < ∏ i ∈ (π.support)ᶜ, M i i := Finset.prod_pos (fun i _ => hdiag i)
    rw [coverTerm_eq_supportCover]
    exact mul_nonneg (main π) hpos.le
  · rw [coverTerm_one]
    exact Finset.prod_pos (fun i _ => hdiag i)

/-- An edge produced by `edgesFrom` runs from one of the walked input species to one of the output
species. -/
private lemma mem_edgesFrom (ss : List (Option Int)) (is outs : List String)
    (ed : SignedEdge) (h : ed ∈ edgesFrom ss is outs) :
    ed.1 ∈ is ∧ ed.2.1 ∈ outs := by
  induction ss generalizing is with
  | nil => simp [edgesFrom] at h
  | cons s ss ih =>
    cases is with
    | nil => simp [edgesFrom] at h
    | cons src is' =>
      simp only [edgesFrom, List.mem_append] at h
      cases h with
      | inl h1 =>
        cases s with
        | none => simp at h1
        | some sign =>
          rw [List.mem_map] at h1
          obtain ⟨dst, hdst, rfl⟩ := h1
          exact ⟨by simp, hdst⟩
      | inr h2 =>
        obtain ⟨hin, hout⟩ := ih is' h2
        exact ⟨List.mem_cons_of_mem _ hin, hout⟩

/-- Every edge of `opEdges` comes from an operator, with its source an input and its target an output
of that operator. -/
private lemma mem_opEdges (g : GRN) (ops : List Node) (ed : SignedEdge)
    (h : ed ∈ opEdges g ops) :
    ∃ op ∈ ops, ed.1 ∈ g.inputsOf op.id ∧ ed.2.1 ∈ g.outputsOf op.id := by
  induction ops with
  | nil => simp [opEdges] at h
  | cons op ops ih =>
    simp only [opEdges, List.mem_append] at h
    cases h with
    | inl h1 =>
      obtain ⟨hin, hout⟩ := mem_edgesFrom _ _ _ _ h1
      exact ⟨op, List.mem_cons_self, hin, hout⟩
    | inr h2 =>
      obtain ⟨op', hop', hin, hout⟩ := ih h2
      exact ⟨op', List.mem_cons_of_mem _ hop', hin, hout⟩

/-- A nonzero interaction-graph edge sign records a real regulation edge. -/
private lemma regulates_of_graphEdgeSign_ne_zero (g : GRN) (s t : g.Species)
    (h : graphEdgeSign g (s : String) (t : String) ≠ 0) : g.regulates s t := by
  unfold graphEdgeSign at h
  cases hf : (g.signedInteractionGraph).find?
      (fun ed => ed.1 == (s : String) && ed.2.1 == (t : String)) with
  | none => rw [hf] at h; simp at h
  | some ed =>
    have hmem : ed ∈ g.signedInteractionGraph := List.mem_of_find?_eq_some hf
    have hcond := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨h1, h2⟩ := hcond
    obtain ⟨op, hop, hin, hout⟩ := mem_opEdges g g.operators ed hmem
    exact ⟨op, hop, by rw [← h1]; exact hin, by rw [← h2]; exact hout⟩

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
    (hconsist : EdgeSignConsistent g)
    (hnopos : hasPositiveLoopEdges (signedInteractionGraph g) = false)
    (σ : Equiv.Perm (Fin n)) (hσ : σ.IsCycle) :
    0 ≤ coverTerm (g.negJac wp e E) σ := by
  classical
  set M := g.negJac wp e E with hMdef
  have hdiagpos : ∀ k, 0 < M k k := negJac_diag_pos g wp hreg e E z hE hz hmono hconsist hnopos
  rcases eq_or_ne (∏ i, M (σ i) i) 0 with hprod0 | hprodne
  · -- some orbit factor is `0` (an absent edge): the whole cover term vanishes
    simp [coverTerm, hprod0]
  · -- all orbit factors are nonzero, so every orbit step is a real edge
    have hfac : ∀ i, M (σ i) i ≠ 0 := by
      intro i hi0
      exact hprodne (Finset.prod_eq_zero (Finset.mem_univ i) hi0)
    -- per-orbit-step facts: the step is a real edge and the entry sign is the negated edge sign
    have hstepfacts : ∀ i ∈ σ.support,
        g.regulates (e i) (e (σ i)) ∧
        M (σ i) i = -(graphEdgeSign g (e i) (e (σ i)) : ℝ) * |M (σ i) i| := by
      intro i hi
      have hne : σ i ≠ i := Equiv.Perm.mem_support.mp hi
      have hmne : M (σ i) i ≠ 0 := hfac i
      obtain ⟨hpos, hneg, hzero0⟩ :=
        negJac_offDiag_signMatches g wp hreg e E z hE hz hmono hconsist (σ i) i hne
      have hgne : graphEdgeSign g (e i) (e (σ i)) ≠ 0 := fun h0 => hmne (hzero0 h0)
      have hregi : g.regulates (e i) (e (σ i)) :=
        regulates_of_graphEdgeSign_ne_zero g (e i) (e (σ i)) hgne
      have hpm : graphEdgeSign g (e i) (e (σ i)) = 1 ∨ graphEdgeSign g (e i) (e (σ i)) = -1 :=
        graphEdgeSign_eq_one_or_neg_one g (e i) (e (σ i)) hmono hgne
      refine ⟨hregi, ?_⟩
      rcases hpm with h1 | h1
      · have hmlt : M (σ i) i < 0 := lt_of_le_of_ne (hpos (by rw [h1]; norm_num)) hmne
        rw [h1]; push_cast; rw [abs_of_neg hmlt]; ring
      · have hmgt : 0 < M (σ i) i := lt_of_le_of_ne (hneg (by rw [h1]; norm_num)) (Ne.symm hmne)
        rw [h1]; push_cast; rw [abs_of_pos hmgt]; ring
    have hstepne : ∀ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) ≠ 0 := by
      intro i hi
      have hne : σ i ≠ i := Equiv.Perm.mem_support.mp hi
      obtain ⟨_, _, hzero0⟩ :=
        negJac_offDiag_signMatches g wp hreg e E z hE hz hmono hconsist (σ i) i hne
      exact fun h0 => (hfac i) (hzero0 h0)
    have peri : ∀ i ∈ σ.support,
        M (σ i) i = -(graphEdgeSign g (e i) (e (σ i)) : ℝ) * |M (σ i) i| :=
      fun i hi => (hstepfacts i hi).2
    -- the orbit's graph-sign product is nonpositive (no positive loop)
    have hPmem := cycleSign_mem_cycleSignsEdges g e hconsist σ hσ hstepne
    have hPnonpos : (∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i))) ≤ 0 :=
      cycleSignsEdges_nonpos_of_noPositiveLoop _ hnopos _ hPmem
    have hcast : ((∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) : ℤ) : ℝ) ≤ 0 :=
      Int.cast_nonpos.mpr hPnonpos
    -- the diagonal and magnitude products are strictly positive
    have hApos : 0 < ∏ i ∈ σ.support, |M (σ i) i| :=
      Finset.prod_pos (fun i _ => abs_pos.mpr (hfac i))
    have hDpos : 0 < ∏ i ∈ σ.supportᶜ, M i i := Finset.prod_pos (fun i _ => hdiagpos i)
    -- split the Leibniz diagonal product over the orbit and its fixed points
    have hsplit : (∏ i, M (σ i) i)
        = (∏ i ∈ σ.support, M (σ i) i) * (∏ i ∈ σ.supportᶜ, M i i) := by
      rw [← Finset.prod_mul_prod_compl σ.support (fun i => M (σ i) i)]
      congr 1
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have hfix : σ i = i := by
        by_contra hne
        exact (Finset.mem_compl.mp hi) (Equiv.Perm.mem_support.mpr hne)
      rw [hfix]
    -- the orbit product factors into the length parity, the graph-sign product, and magnitudes
    have hsupp : (∏ i ∈ σ.support, M (σ i) i)
        = ((-1 : ℝ) ^ σ.support.card
            * ((∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) : ℤ) : ℝ))
          * (∏ i ∈ σ.support, |M (σ i) i|) := by
      rw [Finset.prod_congr rfl peri, Finset.prod_mul_distrib]
      congr 1
      rw [Finset.prod_congr rfl (fun i _ =>
            (neg_one_mul (graphEdgeSign g (e i) (e (σ i)) : ℝ)).symm),
          Finset.prod_mul_distrib, Finset.prod_const, Int.cast_prod]
    have ht : (-1 : ℝ) ^ σ.support.card * (-1 : ℝ) ^ σ.support.card = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have hcoeff : ((coverCoeff σ : ℤ) : ℝ) = -(-1 : ℝ) ^ σ.support.card := by
      have hs : coverCoeff σ = -(-1 : ℤˣ) ^ σ.support.card := by
        rw [coverCoeff_eq_sign]; exact hσ.sign
      rw [hs]; norm_cast
    -- assemble: the parity cancels the `γ − E` sign flips, leaving `-(graph sign product) · (positive)`
    have hval : (-(-1 : ℝ) ^ σ.support.card)
          * ((((-1 : ℝ) ^ σ.support.card
              * ((∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) : ℤ) : ℝ))
              * (∏ i ∈ σ.support, |M (σ i) i|)) * (∏ i ∈ σ.supportᶜ, M i i))
        = (-((∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) : ℤ) : ℝ))
          * ((∏ i ∈ σ.support, |M (σ i) i|) * (∏ i ∈ σ.supportᶜ, M i i)) := by
      linear_combination (-(((∏ i ∈ σ.support, graphEdgeSign g (e i) (e (σ i)) : ℤ) : ℝ))
        * (∏ i ∈ σ.support, |M (σ i) i|) * (∏ i ∈ σ.supportᶜ, M i i)) * ht
    simp only [coverTerm]
    rw [hcoeff, hsplit, hsupp, hval]
    apply mul_nonneg
    · rw [neg_nonneg]; exact hcast
    · exact le_of_lt (mul_pos hApos hDpos)

end GRN
