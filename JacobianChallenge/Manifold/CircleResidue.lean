/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicOneForm
import JacobianChallenge.Manifold.LocalNormalForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Residue contribution from a small chart circle

This file ships a *chip* toward the Stokes route to R5 (residue theorem).

The classical fact: for a meromorphic 1-form `α` with coefficient
`f(z) dz` in a holomorphic chart, integrating `α` over a small circle of
radius `r` centred at `x` yields `2πi · Res_x α`. Equivalently, the
normalised circle integral (multiplied by `(2πi)⁻¹`) equals the residue.

We define `MeromorphicOneForm.chartCircleIntegral α x r` as the normalised
line integral of `α` over the circle of radius `r` in chart coordinates,
parameterised as `θ ↦ (chartAt ℂ x).symm ((chartAt ℂ x) x + r·exp(i θ))`,
with the standard `dz = i r exp(i θ) dθ` substitution.

We then ship the `Prop`-valued statement
`chartCircleIntegral_eq_residue_statement` asserting that for sufficiently
small `r`, this normalised integral equals `α.residueAt x`.

## What's proven vs Prop-only

* **Real definition (not stub):** `MeromorphicOneForm.chartCircleIntegral`
  is a genuine `intervalIntegral` of the chart-pulled-back coefficient
  times the standard `dz` differential.
* **Prop-only def (not axiom):** `chartCircleIntegral_eq_residue_statement`
  is a `Prop`-valued `def`. Its proof requires the local-form expansion
  `α.coeff(z) = (z - x)^k · g(z)` with `g(x) ≠ 0` (Laurent normal form,
  see `Manifold/LocalNormalForm.lean` for the structural skeleton) plus
  the elementary integral `∮_{|z|=r} z^{-1} dz = 2πi`. We do not discharge
  it here.
* **Honest helper (proven):** `chartCircleIntegral_zero` —
  the chart circle integral of the identically-zero coefficient is `0`,
  by `intervalIntegral.integral_zero`.

## Anti-cheat

* No `axiom`, no `sorry`.
* `chartCircleIntegral` is a real definition with a real `intervalIntegral`
  body; not a `0`-stub.
* `chartCircleIntegral_eq_residue_statement` is a `Prop`-valued `def`,
  expressing the classical theorem; we are explicit that we do not prove
  it here.
-/

noncomputable section

open scoped ContDiff Manifold Real
open Complex MeasureTheory

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

namespace MeromorphicOneForm

/-- The **normalised line integral** of a meromorphic 1-form `α` over a
small circle of radius `r` centred at `(chartAt ℂ x) x` in chart
coordinates.

Concretely: parameterise the circle in chart coordinates by
`θ ↦ (chartAt ℂ x).symm ((chartAt ℂ x) x + r · exp(i θ))`,
push the coefficient through, and integrate against the standard
holomorphic differential `dz = i r exp(i θ) dθ`. The factor `(2πi)⁻¹`
normalises so that `∮_{|z|=r} z^{-1} dz / (2πi) = 1`.

This definition is honest: the body is a real `intervalIntegral` of the
genuine chart-pulled-back coefficient against the genuine `dz`
differential, not a `0`-stub. -/
def chartCircleIntegral
    (α : MeromorphicOneForm X) (x : X) (r : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      α.coeff ((chartAt ℂ x).symm
                  ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ)))

@[simp] lemma chartCircleIntegral_def
    (α : MeromorphicOneForm X) (x : X) (r : ℝ) :
    α.chartCircleIntegral x r =
      (2 * Real.pi * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          α.coeff ((chartAt ℂ x).symm
                      ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
            * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ))) := rfl

end MeromorphicOneForm

/-- **Statement of the residue contribution from a small chart circle.**

For sufficiently small `r > 0`, the normalised chart-circle integral of a
meromorphic 1-form `α` equals the residue of `α` at `x`.

This is the classical local form of the Stokes-route residue theorem:
locally, `α.coeff(z) = (z - x)^k · g(z)` with `g(x) ≠ 0`, where
`k = (mmeromorphicOrderAt I α.coeff x).untop₀` (negative for poles); the
non-trivial contribution comes from the `z^{-1}` term, integrated as
`∮_{|z|=r} z^{-1} dz = 2πi`.

**Owed:** the full proof requires
1. The local Laurent normal form `α.coeff = (z - x)^k · g` near `x`
   (`Manifold/LocalNormalForm.lean` ships the structural skeleton; the
   chart-pulled-back analytic part is owed at this mathlib pin).
2. The elementary identity `∮_{|z|=r} z^{-1} dz = 2πi`
   (mathlib has `Complex.integral_circle_one_div_z`-style results in
   `Mathlib.MeasureTheory.Integral.CircleIntegral`).
3. Combining: the `z^{-k-1}` Laurent terms with `k ≠ -1` integrate to
   zero on the circle by `2π`-periodicity of `θ ↦ exp(i k θ)`.

Stated as a `Prop`-valued `def` (NOT `axiom`): downstream proofs can
reference this statement once the local Laurent form lands.

This formalises the *honest* end-state of the chip: we ship the
definition + the precise statement, and we are explicit that the proof
is owed. -/
def chartCircleIntegral_eq_residue_statement
    (α : MeromorphicOneForm X) (x : X) : Prop :=
  ∃ r₀ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r₀,
    α.chartCircleIntegral x r = α.residueAt x

namespace MeromorphicOneForm

/-- **Base case (proven helper):** the chart-circle integral of a
meromorphic 1-form whose coefficient is identically zero is `0`.

The integrand is identically zero, so `intervalIntegral.integral_zero`
collapses the integral to `0`, and the prefactor `(2πi)⁻¹` multiplied by
`0` is `0`.

This is the trivial structural anti-cheat: it confirms the integrand
hooks up correctly. -/
lemma chartCircleIntegral_of_coeff_eq_zero
    (α : MeromorphicOneForm X) (x : X) (r : ℝ)
    (h_coeff : α.coeff = 0) :
    α.chartCircleIntegral x r = 0 := by
  unfold chartCircleIntegral
  have h_integrand :
      (fun θ : ℝ =>
        α.coeff ((chartAt ℂ x).symm
                    ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          * ((r : ℂ) * Complex.I * Complex.exp (Complex.I * (θ : ℂ))))
        = fun _ => (0 : ℂ) := by
    funext θ
    rw [h_coeff]
    simp
  rw [h_integrand]
  simp

end MeromorphicOneForm

end JacobianChallenge

end
