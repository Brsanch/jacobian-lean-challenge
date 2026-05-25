/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernel
import JacobianChallenge.Analysis.InvNormIntegrability

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Chip 1c: integrability of the Pompeiu integrand for continuous compactly-supported `α`

For continuous `α : ℂ → ℂ` with compact support and any base point `z`,
the Pompeiu integrand

  `pompeiuIntegrand α z ζ = α ζ * (ζ - z)⁻¹`

is integrable on `ℂ` against Lebesgue measure. This combines Chip 1a's
translation reduction `integrableOn_inv_norm_sub_iff_origin` with
Chip 1b's polar bound `integrableOn_inv_norm_closedBall`, together with
boundedness of `α` (continuous on its compact support).

## Main result

* `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`

## Proof sketch

1. `Continuous.bounded_above_of_compact_support` gives `M` with
   `‖α x‖ ≤ M` for all `x`.
2. `HasCompactSupport.isBounded.subset_closedBall` gives `R` with
   `tsupport α ⊆ closedBall 0 R`.
3. Outside `closedBall 0 R`, `α = 0`, so the integrand vanishes.
4. Inside, `‖integrand ζ‖ₑ ≤ ENNReal.ofReal M · ‖(‖ζ - z‖⁻¹ : ℝ)‖ₑ`
   (using `‖w⁻¹‖ₑ = ‖(‖w‖⁻¹ : ℝ)‖ₑ` for `w : ℂ`).
5. `closedBall 0 R ⊆ closedBall z (R + ‖z‖)` by the triangle
   inequality; combine Chip 1a's `integrableOn_inv_norm_sub_iff_origin`
   with Chip 1b's `integrableOn_inv_norm_closedBall (R + ‖z‖)` and
   `IntegrableOn.mono_set` to get integrability of `‖ζ - z‖⁻¹` on
   `closedBall 0 R`.
6. Dominate and conclude.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## Pointwise enorm identity for complex inverses -/

/-- For any complex `w`, `‖w⁻¹‖ₑ` equals the `enorm` of the real number
`‖w‖⁻¹`. Both sides are `ENNReal.ofReal ‖w‖⁻¹` (zero at `w = 0` by the
convention `0⁻¹ = 0` in both `ℂ` and `ℝ`). -/
private lemma enorm_inv_complex_eq_enorm_inv_norm_real (w : ℂ) :
    ‖w⁻¹‖ₑ = ‖(‖w‖⁻¹ : ℝ)‖ₑ := by
  rw [← ofReal_norm_eq_enorm, norm_inv,
    Real.enorm_eq_ofReal (inv_nonneg.mpr (norm_nonneg _))]

/-! ## Geometric inclusion -/

/-- The closed disk of radius `R` centred at the origin is contained
in the closed disk of radius `R + ‖z‖` centred at `z`. -/
private lemma closedBall_zero_subset_closedBall_at (R : ℝ) (z : ℂ) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.closedBall z (R + ‖z‖) := by
  intro ζ hζ
  rw [Metric.mem_closedBall, dist_zero_right] at hζ
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
  have : ‖z - ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le _ _
  linarith

/-! ## Integrability of `‖ζ - z‖⁻¹` on a closed disk at the origin -/

/-- Chip 1a translation reduction + Chip 1b polar bound +
`IntegrableOn.mono_set` give integrability of `‖ζ - z‖⁻¹` on the
closed disk `closedBall 0 R`. -/
private lemma integrableOn_inv_norm_sub_closedBall_zero (R : ℝ) (z : ℂ) :
    IntegrableOn (fun ζ : ℂ => ‖ζ - z‖⁻¹) (Metric.closedBall (0 : ℂ) R) volume := by
  have h_at_z : IntegrableOn (fun ζ : ℂ => ‖ζ - z‖⁻¹)
      (Metric.closedBall z (R + ‖z‖)) volume :=
    (integrableOn_inv_norm_sub_iff_origin z (R + ‖z‖)).mpr
      (integrableOn_inv_norm_closedBall (R + ‖z‖))
  exact h_at_z.mono_set (closedBall_zero_subset_closedBall_at R z)

/-! ## Main theorem -/

/-- **Chip 1c — Integrability of the Pompeiu integrand for continuous
compactly-supported `α`.** Combines Chip 1a's translation reduction,
Chip 1b's polar bound, and boundedness of `α`. -/
theorem integrable_pompeiuIntegrand_of_continuous_hasCompactSupport
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Integrable (pompeiuIntegrand α z) volume := by
  -- M : uniform bound on ‖α‖ over all of ℂ.
  obtain ⟨M, hM⟩ := h_cont.bounded_above_of_compact_support h_supp
  have h_M_nonneg : 0 ≤ M := (norm_nonneg (α 0)).trans (hM 0)
  -- R : radius such that tsupport α ⊆ closedBall 0 R.
  obtain ⟨R, hR_subset⟩ := h_supp.isBounded.subset_closedBall (0 : ℂ)
  -- Integrability of ‖ζ - z‖⁻¹ on the closed disk at the origin.
  have h_int_inv := integrableOn_inv_norm_sub_closedBall_zero R z
  refine ⟨aestronglyMeasurable_pompeiuIntegrand_snd h_cont z, ?_⟩
  -- HasFiniteIntegral: bound via the lintegral.
  show ∫⁻ ζ, ‖pompeiuIntegrand α z ζ‖ₑ ∂(volume : Measure ℂ) < (⊤ : ℝ≥0∞)
  -- Pointwise: ‖integrand ζ‖ₑ ≤ (closedBall 0 R).indicator (fun ζ => M · ‖‖ζ-z‖⁻¹‖ₑ) ζ.
  have h_pt : ∀ ζ : ℂ,
      ‖pompeiuIntegrand α z ζ‖ₑ ≤
        (Metric.closedBall (0 : ℂ) R).indicator
          (fun ζ : ℂ => ENNReal.ofReal M * ‖(‖ζ - z‖⁻¹ : ℝ)‖ₑ) ζ := by
    intro ζ
    by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R
    · -- Inside: bound by M · ‖‖ζ - z‖⁻¹‖ₑ.
      rw [Set.indicator_of_mem hζ]
      unfold pompeiuIntegrand
      rw [enorm_mul, ← enorm_inv_complex_eq_enorm_inv_norm_real]
      have h_alpha_bound : ‖α ζ‖ₑ ≤ ENNReal.ofReal M := by
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (hM ζ)
      exact mul_le_mul' h_alpha_bound le_rfl
    · -- Outside: ζ ∉ tsupport α, so α ζ = 0 ⇒ integrand ζ = 0.
      rw [Set.indicator_of_notMem hζ]
      have h_notMem_supp : ζ ∉ tsupport α := fun h => hζ (hR_subset h)
      have h_α0 : α ζ = 0 := image_eq_zero_of_notMem_tsupport h_notMem_supp
      unfold pompeiuIntegrand
      simp [h_α0]
  -- Integrate the bound.
  refine lt_of_le_of_lt (lintegral_mono h_pt) ?_
  rw [lintegral_indicator (Metric.isClosed_closedBall.measurableSet),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Now: ENNReal.ofReal M * ∫⁻ ζ in closedBall 0 R, ‖‖ζ - z‖⁻¹‖ₑ < ⊤.
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- The remaining factor is the lintegral underlying `h_int_inv.hasFiniteIntegral`.
  exact h_int_inv.2

end JacobianChallenge.PompeiuKernel

end
