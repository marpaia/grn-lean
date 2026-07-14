import Mathlib
import GRN.Dynamics.GRNEc50
import GRN.Dynamics.Spin

/-!
# Tier 2 — the reconvergent (sign-consistent) sensor

A sensor GRN need not be a pure activation cascade: it may mix activation and repression and reconverge,
yet still be a monotone system whenever its signed interaction graph is *balanced* (`isMonotoneEdges`).
The classical device (Angeli–Sontag) is a **spin flip**: with the balancing spin `σ : String → Int`
(`GRN.Dynamics.Spin`), pass to flipped coordinates `y_i = σ_i · x_i`. In these coordinates the interpreted
production is cooperative — monotone *increasing* in the flipped inputs — because each edge of sign `s`
contributes `σ_i · s · σ_j = 1` by `balance`.

The dose-response monotonicity then rides the existing feedforward engine (`steadyFam_mono`) in the flipped
frame and unflips to the original coordinates, where the reporter's response is monotone or antitone
according to its own spin `σ_reporter` — the directional response the sensor certificate promises for a
reconvergent circuit.
-/

namespace GRN

open Dynamics Set

/-- σ (a `String → ℝ` spin) takes values `±1` on every regulated species. -/
def IsSpin (σ : String → ℝ) (g : GRN) : Prop := ∀ i : g.Species, σ i.1 = 1 ∨ σ i.1 = -1

/-- σ balances the signed interaction graph: each edge `(j, i, s)` has `σ i = s · σ j`. -/
def Balances (σ : String → ℝ) (g : GRN) : Prop :=
  ∀ e ∈ signedInteractionGraph g, σ e.2.1 = (e.2.2 : ℝ) * σ e.1

/-- A single-input operator that monotonically *represses* its input (`a1 ≤ a0`, with `K > 0`, `n ≥ 0`) —
the repressing counterpart of `Node.MonoActivating`. -/
def _root_.Node.MonoRepressing (op : Node) : Prop :=
  match op.kind with
  | .receiver | .hill1 =>
      0 < op.rparam "K" 1 ∧ 0 ≤ op.rparam "n" 2 ∧
      (op.alphaNums.map (fun q => (q : ℝ))).getD 1 0 ≤ (op.alphaNums.map (fun q => (q : ℝ))).getD 0 0
  | _ => False

/-- An operator with a definite monotone sign: activating or repressing. -/
def _root_.Node.MonoSigned (op : Node) : Prop := op.MonoActivating ∨ op.MonoRepressing

/-- The flipped production of species `i`: the interpreted production read in spin-adjusted coordinates
`x_j = σ_j · y_j`, then scaled by `σ_i`. On a balanced network this is monotone increasing in the flipped
inputs. -/
noncomputable def flipProd (g : GRN) (σ : String → ℝ) (inducer : String → ℝ)
    (i : g.Species) (y : g.Species → ℝ) : ℝ :=
  σ i.1 * g.prodOf inducer i (fun j => σ j.1 * y j)

/-- The flipped production with the chosen inducer's level as a parameter — the flipped-frame production
family fed to `steadyFam`. -/
noncomputable def flipProdParam (g : GRN) (σ : String → ℝ) (base : String → ℝ) (s : String) :
    ℝ → g.Species → (g.Species → ℝ) → ℝ :=
  fun u i y => σ i.1 * g.prodOf (inducerAt base s u) i (fun j => σ j.1 * y j)

/-- Raising the chosen inducer's level does not lower any flipped production: the inducer drives the
network positively in flipped coordinates. -/
def FlipDrive (g : GRN) (σ : String → ℝ) (base : String → ℝ) (s : String) : Prop :=
  ∀ (i : g.Species) (y : g.Species → ℝ) (p q : ℝ), p ≤ q →
    g.flipProdParam σ base s p i y ≤ g.flipProdParam σ base s q i y

-- UNIT: flip-cooperative
/-- **Cooperativity in flipped coordinates.** For a well-posed GRN with a balancing spin `σ` whose every
operator is monotone-signed, the flipped production is monotone increasing in the flipped regulator
coordinates — each edge of sign `s` contributes `σ_i · s · σ_j = 1` by `balance`. -/
theorem flipProd_mono (g : GRN) (σ : String → ℝ) (wp : g.WellPosed)
    (hspin : IsSpin σ g) (hbal : Balances σ g)
    (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (i : g.Species) {y y' : g.Species → ℝ}
    (hnn : ∀ j, 0 ≤ σ j.1 * y j) (hnn' : ∀ j, 0 ≤ σ j.1 * y' j)
    (hle : ∀ j, g.regulates j i → σ j.1 * y j ≤ σ j.1 * y' j) :
    g.flipProd σ wp.inducer i y ≤ g.flipProd σ wp.inducer i y' := by sorry

-- UNIT: flip-propagate
/-- **Propagation in the flipped frame.** Applying `steadyFam_mono` to the flipped production family: the
flipped steady point is monotone in the flipped inducer level. -/
theorem flip_steadyFam_mono (g : GRN) (hac : g.Acyclic) (σ : String → ℝ) (wp : g.WellPosed) (s : String)
    (hspin : IsSpin σ g) (hbal : Balances σ g) (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (hdrive : FlipDrive g σ wp.inducer s) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (i : g.Species) :
    steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) p i
      ≤ steadyFam (g.regulates_wf hac) wp.γ (g.flipProdParam σ wp.inducer s) q i := by sorry

-- UNIT: unflip-response
/-- **The reconvergent dose-response.** Unflipping to the original coordinates: for an acyclic, well-posed,
balanced GRN, the reporter's steady level is monotone in the chosen inducer's level when its spin is `+1`
and antitone when its spin is `-1` — the directional dose-response the sensor certificate promises for a
reconvergent circuit. -/
theorem grn_reconvergent_doseResponse (g : GRN) (hac : g.Acyclic) (σ : String → ℝ) (wp : g.WellPosed)
    (s : String) (reporter : g.Species)
    (hspin : IsSpin σ g) (hbal : Balances σ g) (hsigned : ∀ op ∈ g.operators, op.MonoSigned)
    (hdrive : FlipDrive g σ wp.inducer s) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (σ reporter.1 = 1 →
      steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p reporter
        ≤ steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q reporter) ∧
    (σ reporter.1 = -1 →
      steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) q reporter
        ≤ steadyFam (g.regulates_wf hac) wp.γ
          (fun u i x => g.prodOf (inducerAt wp.inducer s u) i x) p reporter) := by sorry

end GRN
