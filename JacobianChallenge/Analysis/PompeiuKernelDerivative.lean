/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelDirectionalIntegrand
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Chip 2c-main: directional derivative of the Pompeiu kernel

For `α : ℂ → ℂ` of class `C^1` with compact support and any direction
`v : ℂ`, base point `z₀ : ℂ`,

```
HasDerivAt
    (fun t : ℝ => pompeiuKernel α (z₀ + (t : ℝ) • v))
    (pompeiuKernel (αDeriv α v) z₀)
    0
```

Proven by applying `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
to the translated parametric integral
`t ↦ ∫ η, α (η + z₀ + t • v) · η⁻¹` (Chip 2a's form, singularity pinned
at `η = 0`), then identifying the conclusion via Chip 2a in both
the function and the derivative.

## Strategy

1. Chain rule for the integrand: `d/dt α(η + z₀ + t • v) =
   (fderiv ℝ α (η + z₀ + t • v)) v = αDeriv α v (η + z₀ + t • v)`.
2. Uniform derivative bound on `t ∈ Ioo (-1) 1`:
   `‖(fderiv ℝ α (η + z₀ + t • v)) v · η⁻¹‖ ≤ M' · ‖v‖ · ‖η‖⁻¹`
   via `exists_fderiv_norm_bound`.
3. Outside the compact `K := closedBall 0 (R + ‖z₀‖ + ‖v‖ + 1)`, the
   path `η + z₀ + t • v` stays outside `tsupport α` for all `t ∈ (-1,1)`,
   so `fderiv ℝ α (η + z₀ + t • v) = 0` (`fderiv_of_notMem_tsupport`)
   and the derivative integrand vanishes.
4. Dominating function `K.indicator (fun η => M' · ‖v‖ · ‖η‖⁻¹)`,
   integrable via Chip 1b on `K`.
5. Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
6. Identify both sides with `pompeiuKernel` via the inverse of Chip 2a's
   translation identity, scaling by `-(π⁻¹)`.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## Path and chain-rule helpers -/

/-- The path `s : ℝ ↦ η + z₀ + s • v` has derivative `v` everywhere. -/
private lemma hasDerivAt_path (η z₀ v : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => η + z₀ + s • v) v t := by
  have h_smul : HasDerivAt (fun s : ℝ => s • v) v t := by
    have h_id : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id' t
    have := h_id.smul_const v
    simpa using this
  exact h_smul.const_add (η + z₀)

/-- Chain rule for the translated integrand. -/
private lemma hasDerivAt_translated_integrand
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α)
    (η z₀ v : ℂ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => α (η + z₀ + s • v) * η⁻¹)
      ((fderiv ℝ α (η + z₀ + t • v)) v * η⁻¹)
      t := by
  have h_path : HasDerivAt (fun s : ℝ => η + z₀ + s • v) v t :=
    hasDerivAt_path η z₀ v t
  have h_α_diff : HasFDerivAt α (fderiv ℝ α (η + z₀ + t • v))
      (η + z₀ + t • v) :=
    (h_smooth.differentiable (by norm_num) _).hasFDerivAt
  have h_comp : HasDerivAt
      (fun s : ℝ => α (η + z₀ + s • v))
      ((fderiv ℝ α (η + z₀ + t • v)) v)
      t :=
    h_α_diff.comp_hasDerivAt t h_path
  exact h_comp.mul_const η⁻¹

/-! ## Geometric inclusion for the path -/

/-- If `‖η‖ > R + ‖z₀‖ + ‖v‖ + 1` and `|t| < 1`, then
`‖η + z₀ + t • v‖ > R`. -/
private lemma norm_path_gt_R_of_outside
    (R : ℝ) (z₀ v η : ℂ) (t : ℝ)
    (h_norm_η : R + ‖z₀‖ + ‖v‖ + 1 < ‖η‖) (h_t : |t| < 1) :
    R < ‖η + z₀ + t • v‖ := by
  have h_norm_smul : ‖(t : ℝ) • v‖ = |t| * ‖v‖ := by
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ), norm_mul]
    simp
  have h_t_le : |t| ≤ 1 := le_of_lt h_t
  have h_tv_le : ‖t • v‖ ≤ ‖v‖ := by
    rw [h_norm_smul]
    have h_nn : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  have h_z_tv_le : ‖z₀ + t • v‖ ≤ ‖z₀‖ + ‖v‖ :=
    (norm_add_le _ _).trans (by linarith)
  have h_tri : ‖η‖ ≤ ‖η + z₀ + t • v‖ + ‖z₀ + t • v‖ := by
    have h_eq : (η + z₀ + t • v) - (z₀ + t • v) = η := by ring
    have h_step : ‖(η + z₀ + t • v) - (z₀ + t • v)‖
        ≤ ‖η + z₀ + t • v‖ + ‖z₀ + t • v‖ := norm_sub_le _ _
    rw [h_eq] at h_step
    exact h_step
  linarith

/-! ## Vanishing of `fderiv ℝ α` along the path outside `K` -/

/-- If `η + z₀ + t • v ∉ tsupport α`, the derivative `(fderiv ℝ α (η + z₀ + t • v)) v = 0`. -/
private lemma fderiv_apply_eq_zero_of_outside_tsupport
    {α : ℂ → ℂ} {z₀ v η : ℂ} {t : ℝ}
    (h_notMem : (η + z₀ + t • v) ∉ tsupport α) (w : ℂ) :
    (fderiv ℝ α (η + z₀ + t • v)) w = 0 := by
  have h_fderiv_zero : fderiv ℝ α (η + z₀ + t • v) = 0 :=
    fderiv_of_notMem_tsupport ℝ h_notMem
  rw [h_fderiv_zero, ContinuousLinearMap.zero_apply]

/-! ## Main directional derivative theorem (translated form) -/

/-- Apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` to the
translated parametric integral. The result identifies the derivative
in `t` at `t = 0` of `fun t => ∫ η, α (η + z₀ + t • v) · η⁻¹` with
`∫ η, αDeriv α v (η + z₀) · η⁻¹`. -/
private theorem hasDerivAt_translated_integral
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (v z₀ : ℂ) :
    HasDerivAt
      (fun t : ℝ => ∫ η, α (η + z₀ + t • v) * η⁻¹ ∂(volume : Measure ℂ))
      (∫ η, αDeriv α v (η + z₀) * η⁻¹ ∂(volume : Measure ℂ))
      0 := by
  -- Setup constants.
  obtain ⟨M', hM'_nn, hM'⟩ := exists_fderiv_norm_bound h_smooth h_supp
  obtain ⟨R, hR_subset⟩ := h_supp.isBounded.subset_closedBall (0 : ℂ)
  -- Local parameter domain.
  let s : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hs_nhds : s ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  -- Uniform compact for the bound.
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (R + ‖z₀‖ + ‖v‖ + 1)
  let bound : ℂ → ℝ := K.indicator (fun η : ℂ => M' * ‖v‖ * ‖η‖⁻¹)
  -- Define F, F'.
  let F : ℝ → ℂ → ℂ := fun t η => α (η + z₀ + t • v) * η⁻¹
  let F' : ℝ → ℂ → ℂ :=
    fun t η => (fderiv ℝ α (η + z₀ + t • v)) v * η⁻¹
  -- Hypothesis: hF_meas
  have hF_meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) (volume : Measure ℂ) := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h_shift : Measurable (fun η : ℂ => η + (z₀ + t • v)) :=
      measurable_id.add_const _
    have h_eq : (fun η : ℂ => α (η + z₀ + t • v)) =
        α ∘ (fun η : ℂ => η + (z₀ + t • v)) := by
      funext η
      simp [Function.comp_apply, add_assoc]
    have h_meas_α : Measurable (fun η : ℂ => α (η + z₀ + t • v)) := by
      rw [h_eq]
      exact h_smooth.continuous.measurable.comp h_shift
    have h_meas_inv : Measurable (fun η : ℂ => η⁻¹) := measurable_id.inv
    exact (h_meas_α.mul h_meas_inv).aestronglyMeasurable
  -- Hypothesis: hF_int.
  have hF_int : Integrable (F 0) (volume : Measure ℂ) := by
    have h_eq : F 0 = fun η : ℂ => α (η + z₀) * η⁻¹ := by
      funext η; simp [F]
    rw [h_eq]
    exact integrable_translated_pompeiuIntegrand_of_continuous_hasCompactSupport
      h_smooth.continuous h_supp z₀
  -- Hypothesis: hF'_meas.
  have hF'_meas : AEStronglyMeasurable (F' 0) (volume : Measure ℂ) := by
    have h_eq : F' 0 = fun η : ℂ => αDeriv α v (η + z₀) * η⁻¹ := by
      funext η; simp [F', αDeriv]
    rw [h_eq]
    exact (integrable_translated_pompeiuIntegrand_of_continuous_hasCompactSupport
      (αDeriv_continuous h_smooth v) (αDeriv_hasCompactSupport h_supp v)
      z₀).aestronglyMeasurable
  -- Hypothesis: bound_integrable.
  have h_bound_int : Integrable bound (volume : Measure ℂ) := by
    have h_int_inv : IntegrableOn (fun η : ℂ => ‖η‖⁻¹) K (volume : Measure ℂ) :=
      integrableOn_inv_norm_closedBall (R + ‖z₀‖ + ‖v‖ + 1)
    have h_int_scaled :
        IntegrableOn (fun η : ℂ => M' * ‖v‖ * ‖η‖⁻¹) K (volume : Measure ℂ) :=
      h_int_inv.const_mul (M' * ‖v‖)
    exact h_int_scaled.integrable_indicator Metric.isClosed_closedBall.measurableSet
  -- Hypothesis: h_bound. For all η (ae trivially), for all t ∈ s.
  have h_bound : ∀ᵐ η ∂(volume : Measure ℂ), ∀ t ∈ s, ‖F' t η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall (fun η t ht => ?_)
    by_cases hη : η ∈ K
    · -- Inside K: use M' · ‖v‖ · ‖η‖⁻¹.
      show ‖(fderiv ℝ α (η + z₀ + t • v)) v * η⁻¹‖ ≤ bound η
      have h_indicator : bound η = M' * ‖v‖ * ‖η‖⁻¹ := Set.indicator_of_mem hη _
      rw [h_indicator, norm_mul, norm_inv]
      have h_app : ‖(fderiv ℝ α (η + z₀ + t • v)) v‖ ≤ M' * ‖v‖ := by
        refine ((fderiv ℝ α (η + z₀ + t • v)).le_opNorm v).trans ?_
        exact mul_le_mul_of_nonneg_right (hM' _) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right h_app (inv_nonneg.mpr (norm_nonneg _))
    · -- Outside K: fderiv vanishes along the path.
      have h_indicator : bound η = 0 := Set.indicator_of_notMem hη _
      have h_norm_η : R + ‖z₀‖ + ‖v‖ + 1 < ‖η‖ := by
        have h_not_le := hη
        rw [Metric.mem_closedBall, dist_zero_right] at h_not_le
        exact lt_of_not_ge h_not_le
      have h_t_abs : |t| < 1 := abs_lt.mpr ht
      have h_path_norm : R < ‖η + z₀ + t • v‖ :=
        norm_path_gt_R_of_outside R z₀ v η t h_norm_η h_t_abs
      have h_notMem : (η + z₀ + t • v) ∉ tsupport α := by
        intro h_in
        have h_le_R := hR_subset h_in
        rw [Metric.mem_closedBall, dist_zero_right] at h_le_R
        linarith
      have h_zero : (fderiv ℝ α (η + z₀ + t • v)) v = 0 :=
        fderiv_apply_eq_zero_of_outside_tsupport h_notMem v
      show ‖(fderiv ℝ α (η + z₀ + t • v)) v * η⁻¹‖ ≤ bound η
      rw [h_indicator, h_zero, zero_mul, norm_zero]
  -- Hypothesis: h_diff.
  have h_diff : ∀ᵐ η ∂(volume : Measure ℂ), ∀ t ∈ s, HasDerivAt (F · η) (F' t η) t := by
    refine Filter.Eventually.of_forall (fun η t _ht => ?_)
    show HasDerivAt (fun s : ℝ => α (η + z₀ + s • v) * η⁻¹)
      ((fderiv ℝ α (η + z₀ + t • v)) v * η⁻¹) t
    exact hasDerivAt_translated_integrand h_smooth η z₀ v t
  -- Apply the parametric integral derivative theorem.
  have h_apply :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (𝕜 := ℝ) (μ := (volume : Measure ℂ)) (F := F) (x₀ := (0 : ℝ))
      (bound := bound) hs_nhds hF_meas hF_int (F' := F') hF'_meas
      h_bound h_bound_int h_diff
  -- Repackage the conclusion in the desired form.
  have h_F'_eq : F' 0 = fun η : ℂ => αDeriv α v (η + z₀) * η⁻¹ := by
    funext η; simp [F', αDeriv]
  rw [h_F'_eq] at h_apply
  exact h_apply.2

/-! ## Main theorem -/

/-- **Chip 2c-main — Directional derivative of `pompeiuKernel α`.**

For `α ∈ C^1(ℂ → ℂ)` with compact support and any direction `v : ℂ`,

`HasDerivAt (fun t : ℝ => pompeiuKernel α (z₀ + (t : ℝ) • v))
  (pompeiuKernel (αDeriv α v) z₀) 0`.

Proven by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` on
Chip 2a's translated form, with the dominating function from
Chip 2c-prep. Both sides are then identified with `pompeiuKernel`
via the `-(π⁻¹)` scaling from Chip 2a. -/
theorem hasDerivAt_pompeiuKernel_real_direction
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (v z₀ : ℂ) :
    HasDerivAt
      (fun t : ℝ => pompeiuKernel α (z₀ + (t : ℝ) • v))
      (pompeiuKernel (αDeriv α v) z₀)
      0 := by
  -- Translated form of pompeiuKernel composed with z₀ + t • v.
  have h_eq_path : ∀ t : ℝ,
      pompeiuKernel α (z₀ + (t : ℝ) • v) =
        -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z₀ + t • v) * η⁻¹ := by
    intro t
    have h := pompeiuKernel_eq_translated_integrand α (z₀ + (t : ℝ) • v)
    rw [h]
    congr 1
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun η => ?_)
    show α (η + (z₀ + t • v)) * η⁻¹ = α (η + z₀ + t • v) * η⁻¹
    rw [show η + (z₀ + t • v) = η + z₀ + t • v from by ring]
  -- Translated form for the derivative side.
  have h_eq_deriv : pompeiuKernel (αDeriv α v) z₀ =
      -((Real.pi : ℂ)⁻¹) * ∫ η, αDeriv α v (η + z₀) * η⁻¹ :=
    pompeiuKernel_eq_translated_integrand (αDeriv α v) z₀
  -- Apply the integral derivative theorem.
  have h_integral_deriv := hasDerivAt_translated_integral h_smooth h_supp v z₀
  -- Multiply by the constant `-(π⁻¹)`.
  have h_scaled : HasDerivAt
      (fun t : ℝ => -((Real.pi : ℂ)⁻¹) *
        ∫ η, α (η + z₀ + t • v) * η⁻¹ ∂(volume : Measure ℂ))
      (-((Real.pi : ℂ)⁻¹) *
        ∫ η, αDeriv α v (η + z₀) * η⁻¹ ∂(volume : Measure ℂ)) 0 :=
    h_integral_deriv.const_mul (-((Real.pi : ℂ)⁻¹))
  -- Rewrite both sides using the translated form identities.
  rw [show (fun t : ℝ => pompeiuKernel α (z₀ + (t : ℝ) • v))
        = fun t : ℝ => -((Real.pi : ℂ)⁻¹) *
          ∫ η, α (η + z₀ + t • v) * η⁻¹ ∂(volume : Measure ℂ)
      from funext h_eq_path,
    h_eq_deriv]
  exact h_scaled

end JacobianChallenge.PompeiuKernel

end
