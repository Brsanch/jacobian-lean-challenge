/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import JacobianChallenge.Analysis.PompeiuKernelPlaneIntegral
import JacobianChallenge.Analysis.PompeiuIntegrandIntegrability
import JacobianChallenge.Analysis.PompeiuKernelStokesRadial
import JacobianChallenge.Analysis.PompeiuKernelDCTLimit
import JacobianChallenge.Analysis.PompeiuKernel
import JacobianChallenge.Analysis.PompeiuKernelDirectionalIntegrand
import JacobianChallenge.Manifold.PartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3c: plane balance + DCT first summand, radial

This file is the radial-cutoff analog of Chip 3c-E (Sections B + C),
i.e. it replays:

* `balance_plane_eq_zero_radial` — plane-form balance equation with
  `regularizedInvSubRadial` (Section B).
* `tendsto_integral_partialZBar_alpha_mul_regInvSubRadial` — the DCT
  limit on the first summand (Section C).

The proofs are line-for-line replays of Chip 3c-E's, with three
substitutions:

* `regularizedInvSub` ↦ `regularizedInvSubRadial` (3c-F-3a).
* `pompeiuCutoff` ↦ `radialCutoff` (3c-F-1).
* `balance_iteratedIntegral_eq_zero` ↦ `balance_iteratedIntegral_eq_zero_radial`
  (3c-F-3b).

The reasons we cannot reuse 3c-E directly:

* `radialCutoff` is the cutoff whose universal constant (Chip 3c-F-2-final)
  we need downstream.
* `pompeiuCutoff` uses mathlib's abstract `ContDiffBump`, whose radial
  structure is not directly accessible. No universal constant.

The generic plumbing (`partialZBar_continuous`, `partialZBar_hasCompactSupport`,
the Fubini bridge, the dominator integrability from Chip 1c, mathlib's
DCT) is reused unchanged.

## Main results

* `balance_plane_eq_zero_radial : ContDiff ℝ 1 α → HasCompactSupport α →
    0 < ε → 0 < L → tsupport α ⊆ ball 0 L →
    ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ
      + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ = 0`.
* `tendsto_integral_partialZBar_alpha_mul_regInvSubRadial :
    Tendsto (fun ε ↦ ∫ ζ, partialZBar α ζ * regularizedInvSubRadialReal z ε ζ)
      (𝓝[>] 0) (𝓝 (∫ ζ, partialZBar α ζ * (ζ - z)⁻¹))`.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Real Topology

namespace JacobianChallenge.PompeiuKernel

variable {α : ℂ → ℂ}

/-! ## Support and integrability of the radial summands -/

/-- `tsupport (partialZBar α · regularizedInvSubRadial z ε) ⊆ tsupport (partialZBar α)`. -/
lemma tsupport_partialZBar_alpha_mul_regInvSubRadial_subset
    (α : ℂ → ℂ) (z : ℂ) (ε : ℝ) :
    tsupport (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ)
      ⊆ tsupport (partialZBar α) := by
  apply closure_mono
  intro ζ hζ
  rw [Function.mem_support] at hζ ⊢
  intro h_zero
  apply hζ
  rw [h_zero, zero_mul]

/-- `tsupport (α · partialZBar (regularizedInvSubRadial z ε)) ⊆ tsupport α`. -/
lemma tsupport_alpha_mul_partialZBar_regInvSubRadial_subset
    (α : ℂ → ℂ) (z : ℂ) (ε : ℝ) :
    tsupport (fun ζ => α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
      ⊆ tsupport α := by
  apply closure_mono
  intro ζ hζ
  rw [Function.mem_support] at hζ ⊢
  intro h_zero
  apply hζ
  rw [h_zero, zero_mul]

/-- `partialZBar α · regularizedInvSubRadial z ε` is continuous. -/
lemma continuous_partialZBar_alpha_mul_regInvSubRadial
    (h_smooth : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ) := by
  have h_pZ : Continuous (partialZBar α) := partialZBar_continuous h_smooth
  have h_g : Continuous (regularizedInvSubRadial z ε) :=
    (regularizedInvSubRadial_contDiff z hε (n := 0)).continuous
  exact h_pZ.mul h_g

/-- First summand has compact support. -/
lemma hasCompactSupport_partialZBar_alpha_mul_regInvSubRadial
    (h_supp : HasCompactSupport α) (z : ℂ) (ε : ℝ) :
    HasCompactSupport
        (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ) :=
  (partialZBar_hasCompactSupport h_supp).mul_right

/-- First summand is integrable. -/
lemma integrable_partialZBar_mul_regInvSubRadial
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ) := by
  apply (continuous_partialZBar_alpha_mul_regInvSubRadial h_smooth z hε).integrable_of_hasCompactSupport
  exact hasCompactSupport_partialZBar_alpha_mul_regInvSubRadial h_supp z ε

/-- `α · partialZBar (regularizedInvSubRadial z ε)` is continuous. -/
lemma continuous_alpha_mul_partialZBar_regInvSubRadial
    (h_smooth : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun ζ => α ζ * partialZBar (regularizedInvSubRadial z ε) ζ) := by
  have h_α : Continuous α := h_smooth.continuous
  have h_g_smooth : ContDiff ℝ 1 (regularizedInvSubRadial z ε) :=
    regularizedInvSubRadial_contDiff z hε
  have h_pZ_g : Continuous (partialZBar (regularizedInvSubRadial z ε)) :=
    partialZBar_continuous h_g_smooth
  exact h_α.mul h_pZ_g

/-- Second summand has compact support. -/
lemma hasCompactSupport_alpha_mul_partialZBar_regInvSubRadial
    (h_supp : HasCompactSupport α) (z : ℂ) (ε : ℝ) :
    HasCompactSupport
        (fun ζ => α ζ * partialZBar (regularizedInvSubRadial z ε) ζ) :=
  h_supp.mul_right

/-- Second summand is integrable. -/
lemma integrable_alpha_mul_partialZBar_regInvSubRadial
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ζ => α ζ * partialZBar (regularizedInvSubRadial z ε) ζ) := by
  apply (continuous_alpha_mul_partialZBar_regInvSubRadial h_smooth z hε).integrable_of_hasCompactSupport
  exact hasCompactSupport_alpha_mul_partialZBar_regInvSubRadial h_supp z ε

/-! ## Plane-form balance equation (radial) -/

/-- Sum of the two radial summands is integrable. -/
lemma integrable_balance_integrand_radial
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ
      + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ) :=
  (integrable_partialZBar_mul_regInvSubRadial h_smooth h_supp z hε).add
    (integrable_alpha_mul_partialZBar_regInvSubRadial h_smooth h_supp z hε)

/-- Support of the radial balance integrand is in `tsupport α`. -/
lemma tsupport_balance_integrand_radial_subset
    (α : ℂ → ℂ) (z : ℂ) (ε : ℝ) :
    tsupport (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ
        + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
      ⊆ tsupport α := by
  have h_first :
      tsupport (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ)
        ⊆ tsupport α :=
    tsupport_mul_subset_left.trans (tsupport_partialZBar_subset α)
  have h_second :
      tsupport (fun ζ => α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
        ⊆ tsupport α :=
    tsupport_mul_subset_left
  exact (tsupport_add _ _).trans (Set.union_subset h_first h_second)

/-- **Plane-form balance equation, radial cutoff (Chip 3c-F-3c, Section B).**
The radial analog of Chip 3c-E's `balance_plane_eq_zero`. -/
theorem balance_plane_eq_zero_radial
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL_pos : 0 < L) (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
    ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadial z ε ζ
        + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ = 0 := by
  have h_iter :=
    balance_iteratedIntegral_eq_zero_radial h_smooth z hε hL_pos hL_supp
  have h_supp_sum :
      tsupport (fun ζ => partialZBar α ζ * regularizedInvSubRadial z ε ζ
        + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ)
        ⊆ Metric.ball 0 L :=
    (tsupport_balance_integrand_radial_subset α z ε).trans hL_supp
  have h_int_sum := integrable_balance_integrand_radial h_smooth h_supp z hε
  rw [integral_complex_eq_iteratedIntegral_of_tsupport_in_ball
        h_int_sum hL_pos h_supp_sum]
  exact h_iter

/-! ## Section C: DCT limit `ε → 0⁺` of the first summand (radial) -/

/-- Real-parameter wrapper for `regularizedInvSubRadial`: defaults to
`(·-z)⁻¹` for `ε ≤ 0` so the function is `ℝ → ℂ → ℂ`. -/
noncomputable def regularizedInvSubRadialReal (z : ℂ) (ε : ℝ) : ℂ → ℂ :=
  if 0 < ε then regularizedInvSubRadial z ε else fun ζ => (ζ - z)⁻¹

/-- On `0 < ε`, the wrapper agrees with `regularizedInvSubRadial`. -/
lemma regularizedInvSubRadialReal_of_pos {z : ℂ} {ε : ℝ} (hε : 0 < ε) :
    regularizedInvSubRadialReal z ε = regularizedInvSubRadial z ε := by
  unfold regularizedInvSubRadialReal; rw [if_pos hε]

/-- For `ζ ≠ z`, the regularized inverse factor eventually equals
`(ζ-z)⁻¹` as `ε → 0⁺`. -/
lemma regularizedInvSubRadial_eventuallyEq_of_ne (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), regularizedInvSubRadialReal z ε ζ = (ζ - z)⁻¹ := by
  have h_dist_pos : 0 < dist ζ z := dist_pos.mpr hζ
  have h_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < dist ζ z :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds h_dist_pos)
  filter_upwards [h_small, self_mem_nhdsWithin] with ε hε hε_pos
  have hε' : 0 < ε := hε_pos
  have h_notMem : ζ ∉ Metric.ball z ε := by
    rw [Metric.mem_ball]; linarith
  have h_cutoff : radialCutoff z ε ζ = 1 :=
    radialCutoff_eq_one_of_not_mem_ball z hε' h_notMem
  rw [regularizedInvSubRadialReal_of_pos hε']
  show (ζ - z)⁻¹ * ((radialCutoff z ε ζ : ℝ) : ℂ) = (ζ - z)⁻¹
  rw [h_cutoff]; push_cast; ring

/-- Tendsto pointwise on `ζ ≠ z`. -/
lemma tendsto_regularizedInvSubRadialReal_of_ne (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    Tendsto (fun ε : ℝ => regularizedInvSubRadialReal z ε ζ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((ζ - z)⁻¹)) := by
  have h_eq : (fun ε : ℝ => regularizedInvSubRadialReal z ε ζ)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (ζ - z)⁻¹) :=
    regularizedInvSubRadial_eventuallyEq_of_ne z hζ
  exact (Filter.tendsto_congr' h_eq).mpr tendsto_const_nhds

/-- Norm bound on the radial regularized inverse factor. -/
lemma norm_regularizedInvSubRadial_le (z : ℂ) (ε : ℝ) (ζ : ℂ) :
    ‖regularizedInvSubRadial z ε ζ‖ ≤ ‖(ζ - z)⁻¹‖ := by
  show ‖(ζ - z)⁻¹ * ((radialCutoff z ε ζ : ℝ) : ℂ)‖ ≤ ‖(ζ - z)⁻¹‖
  rw [norm_mul]
  have h_cutoff_nonneg : 0 ≤ radialCutoff z ε ζ := radialCutoff_nonneg z ε ζ
  have h_cutoff_le_one : radialCutoff z ε ζ ≤ 1 := radialCutoff_le_one z ε ζ
  have h_cast : ‖((radialCutoff z ε ζ : ℝ) : ℂ)‖ = radialCutoff z ε ζ := by
    rw [Complex.norm_real]; exact abs_of_nonneg h_cutoff_nonneg
  rw [h_cast]
  nlinarith [norm_nonneg ((ζ - z)⁻¹)]

/-- Norm bound on the first balance summand. -/
lemma norm_partialZBar_mul_regInvSubRadial_le
    (α : ℂ → ℂ) (z : ℂ) (ε : ℝ) (ζ : ℂ) :
    ‖partialZBar α ζ * regularizedInvSubRadial z ε ζ‖
      ≤ ‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖ := by
  rw [norm_mul]
  have h := norm_regularizedInvSubRadial_le z ε ζ
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- **DCT limit, first summand, radial (Chip 3c-F-3c, Section C).** As `ε → 0⁺`,
```
∫ ζ : ℂ, partialZBar α ζ · regularizedInvSubRadialReal z ε ζ
  → ∫ ζ : ℂ, partialZBar α ζ · (ζ - z)⁻¹.
```
The right-hand side is `-π · pompeiuKernel (partialZBar α) z`. -/
theorem tendsto_integral_partialZBar_alpha_mul_regInvSubRadial
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Tendsto (fun ε : ℝ =>
        ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubRadialReal z ε ζ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹)) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun ζ => ‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖) ?_ ?_ ?_ ?_
  · -- AEStronglyMeasurable for ε > 0.
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε' : 0 < ε := hε_pos
    rw [regularizedInvSubRadialReal_of_pos hε']
    exact ((partialZBar_continuous h_smooth).aestronglyMeasurable.mul
        (regularizedInvSubRadial_contDiff z hε' (n := 0)).continuous.aestronglyMeasurable)
  · -- Norm bound for ε > 0.
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε' : 0 < ε := hε_pos
    refine Filter.Eventually.of_forall (fun ζ => ?_)
    rw [regularizedInvSubRadialReal_of_pos hε']
    exact norm_partialZBar_mul_regInvSubRadial_le α z ε ζ
  · -- Dominator integrability (reuse from Chip 3c-E).
    exact integrable_dominator_partialZBar h_smooth h_supp z
  · -- Pointwise convergence.
    refine Filter.Eventually.of_forall (fun ζ => ?_)
    by_cases hζ : ζ = z
    · -- ζ = z: both function values and limit value are 0.
      have h_lim_zero : partialZBar α ζ * (ζ - z)⁻¹ = 0 := by
        rw [hζ]; simp
      rw [h_lim_zero]
      have h_F_zero : ∀ ε : ℝ,
          partialZBar α ζ * regularizedInvSubRadialReal z ε ζ = 0 := by
        intro ε
        unfold regularizedInvSubRadialReal
        split_ifs with hε'
        · show partialZBar α ζ * ((ζ - z)⁻¹ * ((radialCutoff z ε ζ : ℝ) : ℂ)) = 0
          rw [hζ]; simp
        · rw [hζ]; simp
      simp_rw [h_F_zero]
      exact tendsto_const_nhds
    · -- ζ ≠ z: wrapper eventually equals (ζ - z)⁻¹.
      have h_tendsto :
          Tendsto (fun ε : ℝ => regularizedInvSubRadialReal z ε ζ)
            (𝓝[>] (0 : ℝ)) (𝓝 ((ζ - z)⁻¹)) :=
        tendsto_regularizedInvSubRadialReal_of_ne z hζ
      exact h_tendsto.const_mul (partialZBar α ζ)

end JacobianChallenge.PompeiuKernel
