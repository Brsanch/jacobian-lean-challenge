/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelTranslation
import JacobianChallenge.Analysis.InvNormIntegralBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Sub-chip 5.5c-III-1b: sup-norm bound on `pompeiuKernel α`

The second analytic primitive of the **Route III (Behnke-Stein
iteration)** arc. Together with Sub-chip 5.5c-III-1a's real-integral
bound `integral_inv_norm_closedBall_le`, this chip ships the
**explicit numeric bound on `‖pompeiuKernel α z‖`** that downstream
contraction-mapping / Schauder estimates consume.

## Main result

`norm_pompeiuKernel_le_of_compact_support_in_ball`:
```
‖pompeiuKernel α z‖ ≤ 2 * (R + ‖z‖) * M
```
when `α : ℂ → ℂ` has `tsupport α ⊆ closedBall 0 R` (`R ≥ 0`) and
`‖α ζ‖ ≤ M` for all `ζ`.

The bound holds without a continuity hypothesis on `α`: if `α` is not
measurable, `pompeiuKernel α z = 0` by Bochner-integral convention and
the bound is trivial; if `α` is measurable, `norm_integral_le_of_norm_le`
against an integrable indicator dominator gives the bound directly.

## Method

Rewrite via Chip 2a's translated form
`pompeiuKernel α z = -(π⁻¹) · ∫ η, α(η + z) · η⁻¹`. The norm factors as
`‖pompeiuKernel α z‖ = π⁻¹ · ‖∫ η, α(η + z) · η⁻¹‖`.

Bound the integral norm by `norm_integral_le_of_norm_le` against the
indicator dominating function
`dom η := (closedBall (-z) R).indicator (fun η => M · ‖η‖⁻¹) η`.
Pointwise domination:

* **`η ∈ closedBall (-z) R`** (i.e., `‖η + z‖ ≤ R`): then
  `‖α(η + z) · η⁻¹‖ = ‖α(η + z)‖ · ‖η‖⁻¹ ≤ M · ‖η‖⁻¹`.
* **`η ∉ closedBall (-z) R`** (i.e., `‖η + z‖ > R`): then
  `η + z ∉ closedBall 0 R ⊇ tsupport α`, so `α(η + z) = 0`, and
  `‖α(η + z) · η⁻¹‖ = 0 = dom η`.

Integrate the indicator dominator:
```
∫ η, dom η = M · ∫ η in closedBall (-z) R, ‖η‖⁻¹
           ≤ M · ∫ η in closedBall 0 (R + ‖z‖), ‖η‖⁻¹
                 (set inclusion: `closedBall (-z) R ⊆ closedBall 0 (R + ‖z‖)`)
           ≤ M · (R + ‖z‖) · 2π     (Sub-chip 5.5c-III-1a)
```

Combine with the `π⁻¹` factor:
```
π⁻¹ · M · (R + ‖z‖) · 2π = 2 · M · (R + ‖z‖) = 2 · (R + ‖z‖) · M.
```

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## Geometric ingredients -/

/-- `closedBall (-z) R ⊆ closedBall 0 (R + ‖z‖)` in `ℂ`. Used to
transport the translated-integrand support bound to a centred ball
for the application of Sub-chip 5.5c-III-1a. -/
lemma closedBall_neg_subset_closedBall_zero (R : ℝ) (z : ℂ) :
    Metric.closedBall (-z) R ⊆ Metric.closedBall (0 : ℂ) (R + ‖z‖) := by
  intro η hη
  rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add] at hη
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖η‖ = ‖(η + z) - z‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖η + z‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ R + ‖z‖ := by linarith

/-- `tsupport α ⊆ closedBall 0 R` (with `R ≥ 0`) implies
`HasCompactSupport α` (since `tsupport α` is closed and bounded in
the proper space `ℂ`). -/
lemma hasCompactSupport_of_tsupport_subset_closedBall
    {α : ℂ → ℂ} (R : ℝ) (h_supp : tsupport α ⊆ Metric.closedBall (0 : ℂ) R) :
    HasCompactSupport α := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R)
    (isClosed_tsupport α) h_supp

/-! ## Pointwise dominator for the translated integrand -/

/-- Pointwise: `‖α(η + z) · η⁻¹‖ ≤ (closedBall (-z) R).indicator
(fun η => M · ‖η‖⁻¹) η` for `η : ℂ`, under
`tsupport α ⊆ closedBall 0 R` and `‖α ζ‖ ≤ M`. -/
private lemma norm_translated_integrand_le_indicator
    {α : ℂ → ℂ} (R : ℝ)
    (h_supp : tsupport α ⊆ Metric.closedBall (0 : ℂ) R)
    (M : ℝ) (h_M : ∀ ζ, ‖α ζ‖ ≤ M) (z η : ℂ) :
    ‖α (η + z) * η⁻¹‖
      ≤ (Metric.closedBall (-z) R).indicator (fun η : ℂ => M * ‖η‖⁻¹) η := by
  by_cases h_mem : η ∈ Metric.closedBall (-z) R
  · -- Inside `closedBall (-z) R`: indicator = `M · ‖η‖⁻¹`.
    rw [Set.indicator_of_mem h_mem]
    rw [norm_mul, norm_inv]
    exact mul_le_mul_of_nonneg_right (h_M (η + z)) (inv_nonneg.mpr (norm_nonneg _))
  · -- Outside: `‖η + z‖ > R` ⇒ `η + z ∉ tsupport α` ⇒ `α (η + z) = 0`.
    rw [Set.indicator_of_notMem h_mem]
    have h_norm_gt : R < ‖η + z‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_neg_eq_add, not_le] at h_mem
      exact h_mem
    have h_not_in_ball : η + z ∉ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]
      exact h_norm_gt
    have h_not_in_tsupport : η + z ∉ tsupport α := fun h => h_not_in_ball (h_supp h)
    have h_α_zero : α (η + z) = 0 := image_eq_zero_of_notMem_tsupport h_not_in_tsupport
    rw [h_α_zero, zero_mul, norm_zero]

/-! ## Integrability of the indicator dominator -/

private lemma integrable_indicator_inv_norm_closedBall
    (R : ℝ) (M : ℝ) (z : ℂ) :
    Integrable
      ((Metric.closedBall (-z) R).indicator (fun η : ℂ => M * ‖η‖⁻¹))
      (volume : Measure ℂ) := by
  have h_int_inv :
      IntegrableOn (fun η : ℂ => ‖η‖⁻¹)
        (Metric.closedBall (-z) R) (volume : Measure ℂ) := by
    -- Reuse Chip 1b's bound applied to the translated ball.
    -- closedBall (-z) R is the preimage of closedBall 0 R under (· - (-z)) = (· + z).
    have h_emb := (Homeomorph.subRight (-z)).measurableEmbedding
    -- Or: use the inclusion + Chip 1b's bound on closedBall 0 (R + ‖z‖).
    refine (integrableOn_inv_norm_closedBall (R + ‖z‖)).mono_set ?_
    exact closedBall_neg_subset_closedBall_zero R z
  have h_int_M : IntegrableOn (fun η : ℂ => M * ‖η‖⁻¹)
      (Metric.closedBall (-z) R) (volume : Measure ℂ) :=
    h_int_inv.const_mul M
  exact h_int_M.integrable_indicator Metric.isClosed_closedBall.measurableSet

/-! ## Main theorem -/

/-- **Sup-norm bound on `pompeiuKernel α`.** For continuous `α : ℂ → ℂ`
with `tsupport α ⊆ closedBall 0 R` (`R ≥ 0`) and uniform norm bound
`‖α ζ‖ ≤ M`, we have
```
‖pompeiuKernel α z‖ ≤ 2 * (R + ‖z‖) * M
```
for every `z : ℂ`.

This is the foundational analytic primitive of the Route III
arc: contraction-mapping / Schauder iterations on the partition-Pompeiu
candidate (`Sub-chip 5.4b`) need explicit sup-norm control on the
local Pompeiu solutions, which this bound provides.

The bound grows linearly in `R + ‖z‖` and is sharp up to constants
(the `1/(ζ - z)` singularity contributes an integral of order
`R + ‖z‖` over the support translated by `z`).
-/
theorem norm_pompeiuKernel_le_of_compact_support_in_ball
    {α : ℂ → ℂ}
    (R : ℝ) (h_R : 0 ≤ R)
    (h_supp : tsupport α ⊆ Metric.closedBall (0 : ℂ) R)
    (M : ℝ) (h_M : ∀ ζ, ‖α ζ‖ ≤ M) (z : ℂ) :
    ‖pompeiuKernel α z‖ ≤ 2 * (R + ‖z‖) * M := by
  -- `M ≥ 0` from `h_M 0 + norm_nonneg`.
  have h_M_nonneg : 0 ≤ M := (norm_nonneg _).trans (h_M 0)
  -- `R + ‖z‖ ≥ 0`.
  have h_R_z_nonneg : 0 ≤ R + ‖z‖ := add_nonneg h_R (norm_nonneg _)
  -- Step 1: rewrite via Chip 2a's translated form.
  rw [pompeiuKernel_eq_translated_integrand α z]
  -- Norm of `-((π : ℂ)⁻¹)` = `π⁻¹`.
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  set I : ℂ := ∫ η : ℂ, α (η + z) * η⁻¹ with hI_def
  -- Step 2: `‖I‖ ≤ M · (R + ‖z‖) · 2π` via dominating indicator integral.
  have h_norm_I_le : ‖I‖ ≤ M * (R + ‖z‖) * (2 * Real.pi) := by
    -- Dominating function: indicator of `closedBall (-z) R`, value `M · ‖η‖⁻¹`.
    set g : ℂ → ℝ := (Metric.closedBall (-z) R).indicator
      (fun η : ℂ => M * ‖η‖⁻¹) with hg_def
    have h_g_int : Integrable g (volume : Measure ℂ) :=
      integrable_indicator_inv_norm_closedBall R M z
    have h_pt : ∀ η : ℂ, ‖α (η + z) * η⁻¹‖ ≤ g η :=
      fun η => norm_translated_integrand_le_indicator R h_supp M h_M z η
    have h_le_g_integral :
        ‖I‖ ≤ ∫ η, g η ∂(volume : Measure ℂ) := by
      refine norm_integral_le_of_norm_le h_g_int (Filter.Eventually.of_forall h_pt)
    -- Compute `∫ η, g η`.
    have h_g_integral :
        ∫ η, g η ∂(volume : Measure ℂ)
          = M * ∫ η in Metric.closedBall (-z) R, ‖η‖⁻¹ ∂(volume : Measure ℂ) := by
      rw [hg_def]
      rw [MeasureTheory.integral_indicator Metric.isClosed_closedBall.measurableSet]
      rw [MeasureTheory.integral_const_mul]
    rw [h_g_integral] at h_le_g_integral
    -- Bound `∫ η in closedBall (-z) R, ‖η‖⁻¹ ≤ ∫ η in closedBall 0 (R + ‖z‖), ‖η‖⁻¹`.
    have h_int_inv_larger :
        IntegrableOn (fun η : ℂ => ‖η‖⁻¹)
          (Metric.closedBall (0 : ℂ) (R + ‖z‖)) (volume : Measure ℂ) :=
      integrableOn_inv_norm_closedBall (R + ‖z‖)
    have h_nonneg_inv : 0 ≤ᵐ[(volume : Measure ℂ).restrict
        (Metric.closedBall (0 : ℂ) (R + ‖z‖))] (fun η : ℂ => ‖η‖⁻¹) :=
      Filter.Eventually.of_forall (fun η => inv_nonneg.mpr (norm_nonneg _))
    have h_subset_ae :
        (Metric.closedBall (-z) R) ≤ᵐ[(volume : Measure ℂ)]
          (Metric.closedBall (0 : ℂ) (R + ‖z‖)) :=
      Filter.Eventually.of_forall (closedBall_neg_subset_closedBall_zero R z)
    have h_setIntegral_mono :
        ∫ η in Metric.closedBall (-z) R, ‖η‖⁻¹ ∂(volume : Measure ℂ)
          ≤ ∫ η in Metric.closedBall (0 : ℂ) (R + ‖z‖), ‖η‖⁻¹ ∂(volume : Measure ℂ) :=
      MeasureTheory.setIntegral_mono_set h_int_inv_larger h_nonneg_inv h_subset_ae
    -- Apply Sub-chip 5.5c-III-1a.
    have h_chip_iiia :
        ∫ η in Metric.closedBall (0 : ℂ) (R + ‖z‖), ‖η‖⁻¹ ∂(volume : Measure ℂ)
          ≤ (R + ‖z‖) * (2 * Real.pi) :=
      integral_inv_norm_closedBall_le (R + ‖z‖) h_R_z_nonneg
    -- Combine: ‖I‖ ≤ M · (R + ‖z‖) · 2π.
    calc ‖I‖
        ≤ M * ∫ η in Metric.closedBall (-z) R, ‖η‖⁻¹ ∂(volume : Measure ℂ) :=
          h_le_g_integral
      _ ≤ M * ∫ η in Metric.closedBall (0 : ℂ) (R + ‖z‖), ‖η‖⁻¹ ∂(volume : Measure ℂ) :=
          mul_le_mul_of_nonneg_left h_setIntegral_mono h_M_nonneg
      _ ≤ M * ((R + ‖z‖) * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left h_chip_iiia h_M_nonneg
      _ = M * (R + ‖z‖) * (2 * Real.pi) := by ring
  -- Step 3: combine the `π⁻¹` factor and conclude.
  have h_pi_inv_nonneg : (0 : ℝ) ≤ Real.pi⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  calc Real.pi⁻¹ * ‖I‖
      ≤ Real.pi⁻¹ * (M * (R + ‖z‖) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left h_norm_I_le h_pi_inv_nonneg
    _ = 2 * (R + ‖z‖) * M := by
        have h_pi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp

end JacobianChallenge.PompeiuKernel

end
