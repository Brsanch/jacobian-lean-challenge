/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Chip 1b: integrability of `‖ζ‖⁻¹` on `closedBall 0 R` in `ℂ`

This is the polar-coordinates step in the Pompeiu kernel arc for the
forward leg of Item 14. Together with the translation reduction
`integrableOn_inv_norm_sub_iff_origin` from
`JacobianChallenge.Analysis.PompeiuKernel` (Chip 1a), it gives
integrability of `‖ζ - z‖⁻¹` on any closed ball; that is the key local
fact underlying integrability of the Pompeiu integrand for continuous
compactly-supported `α` (Chip 1c).

## Main result

* `integrableOn_inv_norm_closedBall (R : ℝ) :`
  `IntegrableOn (fun ζ : ℂ => ‖ζ‖⁻¹) (closedBall (0 : ℂ) R) volume`

The bound
`∫⁻ ζ in closedBall 0 R, ‖(‖ζ‖⁻¹ : ℝ)‖ₑ ∂volume ≤ ENNReal.ofReal (max R 0) * ENNReal.ofReal (2 * π)`
is obtained by changing to polar coordinates via
`Complex.lintegral_comp_polarCoord_symm`. The Jacobian factor
`ENNReal.ofReal p.1` cancels the integrand factor
`(ENNReal.ofReal p.1)⁻¹` everywhere on `polarCoord.target`, leaving an
integrand bounded by `1`. The image of `closedBall 0 R` under polar
inversion is contained in `Ioc 0 (max R 0) ×ˢ Ioo (-π) π`, whose
volume is `(max R 0) * 2π`.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## Pointwise norm bound -/

/-- Pointwise inequality between the `enorm` of the real-valued
`‖ζ‖⁻¹` and the `ℝ≥0∞` inverse of the `enorm` of `ζ`.

For `ζ ≠ 0` the inequality is in fact an equality. At `ζ = 0` the
left-hand side is `0` (since `‖0‖⁻¹ = 0⁻¹ = 0` in `ℝ`) and the
right-hand side is `⊤`. -/
private lemma enorm_inv_norm_le_inv_enorm (ζ : ℂ) :
    ‖(‖ζ‖⁻¹ : ℝ)‖ₑ ≤ (‖ζ‖ₑ)⁻¹ := by
  by_cases h : ζ = 0
  · subst h
    simp
  · have h_pos : 0 < ‖ζ‖ := norm_pos_iff.mpr h
    have h_nonneg : 0 ≤ ‖ζ‖⁻¹ := inv_nonneg.mpr h_pos.le
    rw [Real.enorm_eq_ofReal h_nonneg, ← ofReal_norm_eq_enorm,
      ENNReal.ofReal_inv_of_pos h_pos]

/-! ## Polar-coordinate bound on the integrand -/

/-- On the polar target `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`, the
integrand `ENNReal.ofReal p.1 * (closedBall 0 R).indicator (‖·‖ₑ)⁻¹
(polarCoord.symm p)` is bounded above by the indicator of
`Ioc 0 (max R 0) ×ˢ Ioo (-π) π` (the polar image of the closed ball,
plus possibly a measure-zero slit), with constant value `1`. -/
private lemma polar_integrand_bound (R : ℝ) {p : ℝ × ℝ}
    (hp : p ∈ Complex.polarCoord.target) :
    ENNReal.ofReal p.1 *
        (Metric.closedBall (0 : ℂ) R).indicator (fun ζ : ℂ => (‖ζ‖ₑ)⁻¹)
          (Complex.polarCoord.symm p) ≤
      (Set.Ioc (0 : ℝ) (max R 0) ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
        (fun _ => (1 : ℝ≥0∞)) p := by
  -- Unpack `p ∈ polarCoord.target`.
  rw [Complex.polarCoord_target] at hp
  rcases hp with ⟨hp1, hp2⟩
  have h_p1_pos : 0 < p.1 := hp1
  have h_norm_eq : ‖Complex.polarCoord.symm p‖ = p.1 := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos h_p1_pos]
  by_cases h_mem : Complex.polarCoord.symm p ∈ Metric.closedBall (0 : ℂ) R
  · -- In the closed ball: the indicator equals `(‖polarCoord.symm p‖ₑ)⁻¹`.
    rw [Set.indicator_of_mem h_mem]
    have h_le_R : p.1 ≤ R := by
      have h := h_mem
      rw [Metric.mem_closedBall, dist_zero_right, h_norm_eq] at h
      exact h
    have h_in_target : p ∈ Set.Ioc (0 : ℝ) (max R 0) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
      refine ⟨⟨h_p1_pos, h_le_R.trans (le_max_left _ _)⟩, hp2⟩
    rw [Set.indicator_of_mem h_in_target]
    -- Reduce the LHS to `ENNReal.ofReal p.1 * (ENNReal.ofReal p.1)⁻¹ = 1`.
    rw [← ofReal_norm_eq_enorm, h_norm_eq]
    have h_ofR_ne_zero : ENNReal.ofReal p.1 ≠ 0 :=
      (ENNReal.ofReal_pos.mpr h_p1_pos).ne'
    have h_ofR_ne_top : ENNReal.ofReal p.1 ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [ENNReal.mul_inv_cancel h_ofR_ne_zero h_ofR_ne_top]
  · -- Not in the closed ball: indicator is `0`, product is `0`, bound trivial.
    rw [Set.indicator_of_notMem h_mem]
    simp

/-! ## Volume of the polar image rectangle -/

private lemma volume_polar_rect_eq (R : ℝ) :
    (volume : Measure (ℝ × ℝ))
        (Set.Ioc (0 : ℝ) (max R 0) ×ˢ Set.Ioo (-Real.pi) Real.pi) =
      ENNReal.ofReal (max R 0) * ENNReal.ofReal (2 * Real.pi) := by
  rw [Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Ioc,
    Real.volume_Ioo, sub_zero,
    show Real.pi - -Real.pi = 2 * Real.pi by ring]

/-! ## Main lintegral bound -/

private lemma lintegral_inv_enorm_closedBall_le (R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, (‖ζ‖ₑ)⁻¹ ∂(volume : Measure ℂ) ≤
      ENNReal.ofReal (max R 0) * ENNReal.ofReal (2 * Real.pi) := by
  have h_meas : MeasurableSet (Metric.closedBall (0 : ℂ) R) :=
    Metric.isClosed_closedBall.measurableSet
  -- Step 1: rewrite the set lintegral as a global lintegral against the indicator.
  rw [← lintegral_indicator h_meas]
  -- Step 2: apply the polar change of variables in reverse.
  rw [← Complex.lintegral_comp_polarCoord_symm
    ((Metric.closedBall (0 : ℂ) R).indicator (fun ζ : ℂ => (‖ζ‖ₑ)⁻¹))]
  -- Step 3: pointwise bound on `polarCoord.target`.
  refine le_trans
    (setLIntegral_mono' Complex.polarCoord.open_target.measurableSet
      (fun p hp => polar_integrand_bound R hp)) ?_
  -- Step 4: drop the restriction and identify with the rectangle volume.
  refine le_trans (setLIntegral_le_lintegral _ _) ?_
  rw [lintegral_indicator
        ((measurableSet_Ioc).prod (measurableSet_Ioo)),
    setLIntegral_const, volume_polar_rect_eq R, one_mul]

/-! ## Main theorem -/

/-- **Chip 1b — Integrability of `‖ζ‖⁻¹` on a closed disk centred at the
origin in `ℂ`.** Proven via the polar change of variables. The
quantitative bound `∫⁻ ζ in closedBall 0 R, ‖(‖ζ‖⁻¹ : ℝ)‖ₑ ∂volume ≤
(max R 0) * 2π` is recorded as the auxiliary
`lintegral_inv_enorm_closedBall_le`. -/
theorem integrableOn_inv_norm_closedBall (R : ℝ) :
    IntegrableOn (fun ζ : ℂ => ‖ζ‖⁻¹) (Metric.closedBall (0 : ℂ) R) volume := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable.
    exact (measurable_norm.inv).aestronglyMeasurable
  · -- HasFiniteIntegral. `‖‖ζ‖⁻¹‖ₑ ≤ (‖ζ‖ₑ)⁻¹` pointwise, then apply the
    -- lintegral bound.
    refine lt_of_le_of_lt (b := ENNReal.ofReal (max R 0) * ENNReal.ofReal (2 * Real.pi))
      ?_ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    refine le_trans (lintegral_mono fun ζ => enorm_inv_norm_le_inv_enorm ζ) ?_
    exact lintegral_inv_enorm_closedBall_le R

end JacobianChallenge.PompeiuKernel

end
