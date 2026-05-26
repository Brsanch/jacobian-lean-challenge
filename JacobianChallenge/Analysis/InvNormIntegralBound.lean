/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.InvNormIntegrability

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Sub-chip 5.5c-III-1a: real-integral bound for `‖ζ‖⁻¹` on `closedBall 0 r`

The first analytic primitive of the **Route III (Behnke-Stein
iteration)** arc, replacing the OmegaForm partition-sum approach
ruled out by the Forster Ch.14 audit
(`ROUTE_5_5C_FORSTER_AUDIT.md`). This file converts Chip 1b's
`lintegral`-form bound to the `∫`-form bound that downstream
analytic estimates (the sup-norm bound on `pompeiuKernel`,
Schauder-type estimates, contraction-mapping iteration) consume.

## Main result

`integral_inv_norm_closedBall_le`:
```
∫ ζ in closedBall (0 : ℂ) r, ‖ζ‖⁻¹ ∂volume ≤ r * (2 * π)
```
for any `r ≥ 0`.

## Method

The integrand `‖ζ‖⁻¹` is nonneg and (by Chip 1b)
`IntegrableOn (closedBall 0 r) volume`. By
`integral_eq_lintegral_of_nonneg_ae`,
```
∫ ζ in closedBall 0 r, ‖ζ‖⁻¹ ∂volume
  = (∫⁻ ζ in closedBall 0 r, ENNReal.ofReal ‖ζ‖⁻¹ ∂volume).toReal.
```
The lintegrand is bounded pointwise by `(‖ζ‖ₑ)⁻¹` (equality off the
origin; LHS is `0`, RHS is `⊤` at `ζ = 0`), so monotonicity reduces
to Chip 1b's `lintegral_inv_enorm_closedBall_le`. Take `.toReal`
of the resulting `ENNReal.ofReal (r * 2π)` bound.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-- Pointwise: `ENNReal.ofReal (‖ζ‖⁻¹) ≤ (‖ζ‖ₑ)⁻¹` for any `ζ : ℂ`.
At `ζ ≠ 0` this is equality (both equal `(ENNReal.ofReal ‖ζ‖)⁻¹`);
at `ζ = 0` the LHS is `0` and the RHS is `⊤`. -/
private lemma ofReal_inv_norm_le_inv_enorm (ζ : ℂ) :
    ENNReal.ofReal (‖ζ‖⁻¹) ≤ (‖ζ‖ₑ)⁻¹ := by
  by_cases h : ζ = 0
  · subst h
    simp
  · have h_pos : 0 < ‖ζ‖ := norm_pos_iff.mpr h
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_inv_of_pos h_pos]

/-- **Real-integral version of Chip 1b's polar-coordinate bound.** For
any `r ≥ 0`, the integral of `‖ζ‖⁻¹` over `closedBall 0 r` in `ℂ` is
bounded by `r · 2π`.

This is the form of the bound that downstream `pompeiuKernel`
estimates consume (the chip-1b `lintegral` form is only useful for
integrability, not for explicit numeric bounds on the Pompeiu
integral norm). -/
theorem integral_inv_norm_closedBall_le (r : ℝ) (hr : 0 ≤ r) :
    ∫ ζ in Metric.closedBall (0 : ℂ) r, ‖ζ‖⁻¹ ∂(volume : Measure ℂ)
      ≤ r * (2 * Real.pi) := by
  -- Convert real set-integral to lintegral.
  have h_nonneg :
      0 ≤ᵐ[(volume : Measure ℂ).restrict (Metric.closedBall (0 : ℂ) r)]
        (fun ζ : ℂ => ‖ζ‖⁻¹) :=
    Filter.Eventually.of_forall (fun ζ => inv_nonneg.mpr (norm_nonneg _))
  have h_meas : AEStronglyMeasurable (fun ζ : ℂ => ‖ζ‖⁻¹)
      ((volume : Measure ℂ).restrict (Metric.closedBall (0 : ℂ) r)) :=
    (measurable_norm.inv).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae h_nonneg h_meas]
  -- Lintegral pointwise bound: `ENNReal.ofReal (‖ζ‖⁻¹) ≤ (‖ζ‖ₑ)⁻¹`.
  have h_lint_le :
      ∫⁻ ζ in Metric.closedBall (0 : ℂ) r,
            ENNReal.ofReal (‖ζ‖⁻¹) ∂(volume : Measure ℂ)
        ≤ ∫⁻ ζ in Metric.closedBall (0 : ℂ) r,
            (‖ζ‖ₑ)⁻¹ ∂(volume : Measure ℂ) :=
    lintegral_mono (fun ζ => ofReal_inv_norm_le_inv_enorm ζ)
  -- Chip 1b's bound.
  have h_chip1b := lintegral_inv_enorm_closedBall_le r
  have h_max : max r 0 = r := max_eq_left hr
  rw [h_max] at h_chip1b
  -- Combine and convert ENNReal.toReal monotonely.
  have h_combined :
      ∫⁻ ζ in Metric.closedBall (0 : ℂ) r,
            ENNReal.ofReal (‖ζ‖⁻¹) ∂(volume : Measure ℂ)
        ≤ ENNReal.ofReal r * ENNReal.ofReal (2 * Real.pi) :=
    h_lint_le.trans h_chip1b
  have h_2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have h_prod_nonneg : (0 : ℝ) ≤ r * (2 * Real.pi) := mul_nonneg hr h_2pi_nonneg
  have h_combined' :
      ∫⁻ ζ in Metric.closedBall (0 : ℂ) r,
            ENNReal.ofReal (‖ζ‖⁻¹) ∂(volume : Measure ℂ)
        ≤ ENNReal.ofReal (r * (2 * Real.pi)) := by
    rw [ENNReal.ofReal_mul hr]
    exact h_combined
  have h_finite : (ENNReal.ofReal (r * (2 * Real.pi))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_toReal_le := ENNReal.toReal_mono h_finite h_combined'
  rw [ENNReal.toReal_ofReal h_prod_nonneg] at h_toReal_le
  exact h_toReal_le

end JacobianChallenge.PompeiuKernel

end
