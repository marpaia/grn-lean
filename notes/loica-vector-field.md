# The LOICA vector field (reference)

The exact ODE LOICA integrates, transcribed from [RudgeLab/LOICA](https://github.com/RudgeLab/LOICA) so the Lean vector
field matches the simulator that scores candidate designs. Sign conventions here are the source of truth
for `GRN.InteractionGraph`.

## Per-species state equation

For a regulated species (regulator or reporter) with concentration `x`, degradation rate `γ`, and
host growth rate `μ(t)` (`geneproduct.py:43-47`):

```
dx/dt = e(t) − (γ + μ(t)) · x
```

`e(t)` is the summed **expression rate** driving the species: each operator computes a scalar rate and
adds it to every output species' accumulator (`genetic_network.py:135-148`, `geneproduct.py:40-41`);
multiple operators onto one species sum. The output is a production *rate*, not a target level, so the
fixed point is `x* = e / (γ + μ)`, not `x* = e`. With `γ = μ = 0` there is no finite equilibrium. Units
of `alpha` and `Source.rate` are expression rate (MEFL/second).

Integration is explicit forward Euler with `dt = interval / substeps` (`assay.py`), not `solve_ivp`.
The stochastic path uses the same rates as propensities (`genetic_network.py:81-127`).

## Operator expression rates

Let `r = (u/K)^n` for input concentration `u`.

- **Hill1** (`hill1.py:53-57`) and **Receiver** (`receiver.py:54-58`): identical algebra; a receiver's
  input is an external supplement:
  ```
  e = (α₀ + α₁·r) / (1 + r)
  ```
  `α₀` is basal (`u=0`), `α₁` the saturating level (`u→∞`). **Activation iff `α₁ > α₀`, repression iff
  `α₁ < α₀`**: the sign rule `GRN.pairSign` implements.

- **Hill2** (`hill2.py:52-61`), `α` length 4, `K`/`n` length 2, `r₁,r₂` per input, `r₁₂ = r₁·r₂`:
  ```
  e = (α₀ + α₁·r₁ + α₂·r₂ + α₃·r₁₂) / (1 + r₁ + r₂ + r₁₂)
  ```
  `α₀` both-low, `α₃` both-high. Here `α₁` is the coefficient of the *first* input's Hill term and `α₂`
  the second's.

- **Sum** (`sum.py:18-26`), `α` a list of `[basal, regulated]` pairs, one per input:
  ```
  e = Σᵢ (αᵢ₀ + αᵢ₁·rᵢ) / (1 + rᵢ)
  ```

- **Source** (`source.py:41-42`): a constant `e = rate`.

## Hill2 index convention

LOICA wires `hill2` inputs in port order (`simulate.py:151-159`): port 0 → `input_repressor1` (r₁),
port 1 → r₂, and integrates `a₀ + a₁·r₁ + a₂·r₂ + a₃·r₁·r₂`. So `a₁` is port 0's solo coefficient and
`a₂` is port 1's. `grn-lean`'s `operatorInputSigns` reads the vector with this convention: port 0's sign from `[a₁−a₀, a₃−a₂]`, port 1's from `[a₂−a₀, a₃−a₁]`.

## Consequences for the dynamical theorems

- The field is smooth and globally Lipschitz (bounded Hill terms plus the linear `−(γ+μ)x`), but not
  globally bounded, so `crnt-lean`'s `exists_flow` (global-bound hypothesis) does not apply directly;
  route existence through a forward-invariant box (Nagumo) plus Mathlib Picard–Lindelöf.
- A forward-invariant box exists: expression is bounded by `Σ αᵢ,max` and degradation/dilution pulls
  inward, so the nonnegative box `[0, αmax/(γ+μ)]ⁿ` is invariant, the compact region the certificates'
  dynamical claims live on.
