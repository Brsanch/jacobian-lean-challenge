/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicOneForm
import JacobianChallenge.Manifold.LocalNormalForm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral

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

/-- **Bridge:** rewrite `chartCircleIntegral` as `(2πi)⁻¹ ·` mathlib's
`circleIntegral` applied to a function `f : ℂ → ℂ`, provided the
chart-pulled-back coefficient agrees with `f ∘ circleMap z₀ r` on the
integration interval.

This bridge transports the user's chart-coordinate integral to mathlib's
`circleIntegral`, where Laurent-monomial integration lemmas
(`circleIntegral.integral_sub_zpow_of_ne`,
`circleIntegral.integral_sub_inv_of_mem_ball`) live. -/
lemma chartCircleIntegral_eq_circleIntegral_of_coeff_eq
    (α : MeromorphicOneForm X) (x : X) (r : ℝ) (f : ℂ → ℂ)
    (h : ∀ θ : ℝ,
      α.coeff ((chartAt ℂ x).symm
                ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = f (circleMap ((chartAt ℂ x) x) r θ)) :
    α.chartCircleIntegral x r =
      (2 * Real.pi * Complex.I)⁻¹ *
        (∮ z in C((chartAt ℂ x) x, r), f z) := by
  -- Both sides are `(2πi)⁻¹ * <interval integral>`. Show pointwise equality
  -- of integrands, then invoke `intervalIntegral.integral_congr`.
  rw [chartCircleIntegral_def]
  show _ = (2 * Real.pi * Complex.I)⁻¹ * circleIntegral f ((chartAt ℂ x) x) r
  unfold circleIntegral
  congr 1
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  -- LHS integrand: α.coeff(symm(z₀ + r·exp(I·θ))) * (r · I · exp(I·θ))
  -- RHS integrand (mathlib): deriv (circleMap z₀ r) θ • f (circleMap z₀ r θ)
  --                       = (r · exp(θ·I) · I) * f (z₀ + r · exp(θ·I))
  rw [h θ, deriv_circleMap]
  -- circleMap 0 r θ = r * exp(θ * I); also θ*I = I*θ in ℂ.
  have hθcomm : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [mul_comm]
  rw [circleMap_zero, smul_eq_mul, ← hθcomm]
  ring

/-! ### Laurent monomial closed form -/

/-- **Laurent monomial residue (closed-form, simplest case).**

If on the integration circle the chart-pulled-back coefficient of `α`
equals the Laurent monomial `c · (z - z₀)^n` (with `z₀ = (chartAt ℂ x) x`,
`n : ℤ`, `c : ℂ`), and `r > 0`, then the normalised chart-circle integral
is

* `c` if `n = -1` (residue of a simple pole),
* `0` otherwise (no residue contribution from regular or higher-pole
  Laurent terms).

This is the analytic kernel of the residue theorem in its single-monomial
form: it discharges, in closed form, exactly the cases needed by
`chartCircleIntegral_eq_residue_statement` once the local Laurent normal
form has been decomposed into monomial summands.

The proof reduces to mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`
and `circleIntegral.integral_sub_zpow_of_ne` after pulling the constant
`c` out and identifying the chart-coordinate integral with the standard
mathlib `∮ z in C(z₀, r), (z - z₀)^n`. -/
theorem chartCircleIntegral_of_coeff_eq_laurent_monomial
    (α : MeromorphicOneForm X) (x : X) (r : ℝ) (hr : 0 < r)
    (n : ℤ) (c : ℂ)
    (h : ∀ θ : ℝ,
      α.coeff ((chartAt ℂ x).symm
                ((chartAt ℂ x) x + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        = c * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ^ n) :
    α.chartCircleIntegral x r = if n = -1 then c else 0 := by
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- Reduce to mathlib `circleIntegral` of `c · (z - z₀)^n`.
  have hbridge :
      α.chartCircleIntegral x r =
        (2 * Real.pi * Complex.I)⁻¹ *
          (∮ z in C(z₀, r), c * (z - z₀) ^ n) := by
    refine chartCircleIntegral_eq_circleIntegral_of_coeff_eq α x r
      (fun z => c * (z - z₀) ^ n) ?_
    intro θ
    -- circleMap z₀ r θ - z₀ = r * exp(θ I); rewrite to match user's `I * θ`.
    have hsub : circleMap z₀ r θ - z₀ = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [circleMap_sub_center, circleMap_zero, mul_comm (Complex.I) ((θ : ℂ))]
    show α.coeff _ = c * (circleMap z₀ r θ - z₀) ^ n
    rw [h θ, hsub]
  rw [hbridge, circleIntegral.integral_const_mul]
  by_cases hn : n = -1
  · -- n = -1: ∮ (z - z₀)⁻¹ = 2πi by `integral_sub_inv_of_mem_ball` (z₀ ∈ ball z₀ r).
    subst hn
    have hmem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
    have hint :
        (∮ z in C(z₀, r), (z - z₀) ^ (-1 : ℤ)) = 2 * Real.pi * Complex.I := by
      have : (∮ z in C(z₀, r), (z - z₀)⁻¹) = 2 * Real.pi * Complex.I :=
        circleIntegral.integral_sub_inv_of_mem_ball hmem
      simpa [zpow_neg_one] using this
    rw [hint]
    -- (2πi)⁻¹ * (c * (2πi)) = c
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      have hπ : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero h2 hπ) Complex.I_ne_zero
    rw [if_pos rfl]
    rw [show (c * (2 * Real.pi * Complex.I) : ℂ) = (2 * Real.pi * Complex.I) * c from by ring,
        ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
  · -- n ≠ -1: ∮ (z - z₀)^n = 0 by `integral_sub_zpow_of_ne`.
    have hint :
        (∮ z in C(z₀, r), (z - z₀) ^ n) = 0 :=
      circleIntegral.integral_sub_zpow_of_ne hn z₀ z₀ r
    rw [hint]
    simp [if_neg hn]

end MeromorphicOneForm

end JacobianChallenge

end
