/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Chip 2d: ℝ-smoothness of `pompeiuKernel α`

For `α : ℂ → ℂ` of class `C^∞` with compact support, the Pompeiu kernel
`pompeiuKernel α : ℂ → ℂ` is of class `C^∞` in the real-differentiable
sense. The fderiv identity

`fderiv ℝ (pompeiuKernel α) z₀ v = pompeiuKernel (αDeriv α v) z₀`

(`fderiv_pompeiuKernel_apply`) is the inductive engine: differentiation
in the base point `z₀` commutes with the integral, and the resulting
integrand is the Pompeiu integrand of the directional-derivative input
`αDeriv α v`. Iterating, each derivative of `pompeiuKernel α` becomes a
`pompeiuKernel` of a derivative of `α`, and `α ∈ C^k` gives
`pompeiuKernel α ∈ C^k`.

## Strategy

1. **Translated integrand HasFDerivAt** — Apply
   `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le` with
   complex parameter `z : ℂ` to the translated form
   `(fun z => ∫ η, α (η + z) * η⁻¹ ∂vol)` from Chip 2a. The CLM-valued
   integrand is `F' z η := (η⁻¹ : ℂ) • fderiv ℝ α (η + z)`. The
   uniform-in-z dominating function is `K.indicator (M' · ‖η‖⁻¹)` with
   `K := closedBall 0 (R + ‖z₀‖ + 1)`, paralleling Chip 2c-main's setup.
2. **HasFDerivAt for `pompeiuKernel α`** — Scale by `-(π⁻¹)` via
   `HasFDerivAt.const_mul`.
3. **Apply identity** — `fderiv ℝ (pompeiuKernel α) z₀ v` equals
   `pompeiuKernel (αDeriv α v) z₀` by `ContinuousLinearMap.integral_apply`
   and the translated form identity (Chip 2a) applied to
   `αDeriv α v`.
4. **ContDiff induction on `n : ℕ`** — Base case `n = 0` is Chip 2b
   (continuity). Successor `n+1` via `contDiff_succ_iff_fderiv_apply`
   (`ℂ` is finite-dimensional over `ℝ`): differentiability is the lift
   to `HasFDerivAt`, and for each `v`,
   `(fun z => fderiv ℝ (pompeiuKernel α) z v) = pompeiuKernel (αDeriv α v)`
   is `C^n` by the IH applied to `αDeriv α v` (which is `C^n` with
   compact support whenever `α` is `C^(n+1)` with compact support).
5. **C^∞ corollary** — `contDiff_infty` reduces to the `ℕ` case.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ContDiff

namespace JacobianChallenge.PompeiuKernel

/-! ## Section 1: CLM-valued integrand for the parametric integral derivative

`pompeiuFDerivIntegrand α z η : ℂ →L[ℝ] ℂ` is `η⁻¹ • fderiv ℝ α (η + z)`.
On evaluation at `v : ℂ`, it equals `η⁻¹ * (fderiv ℝ α (η + z)) v`,
which by `mul_comm` is `(fderiv ℝ α (η + z)) v * η⁻¹` — the pointwise
derivative of the translated integrand from Chip 2a. -/

/-- CLM-valued integrand: `(η⁻¹ : ℂ) • fderiv ℝ α (η + z)`. -/
def pompeiuFDerivIntegrand (α : ℂ → ℂ) (z η : ℂ) : ℂ →L[ℝ] ℂ :=
  (η⁻¹ : ℂ) • fderiv ℝ α (η + z)

@[simp]
lemma pompeiuFDerivIntegrand_apply (α : ℂ → ℂ) (z η v : ℂ) :
    pompeiuFDerivIntegrand α z η v = η⁻¹ * (fderiv ℝ α (η + z)) v := by
  unfold pompeiuFDerivIntegrand
  simp [smul_eq_mul]

/-- Pointwise norm bound: `‖F' z η‖ = ‖η⁻¹‖ · ‖fderiv ℝ α (η + z)‖`. -/
private lemma norm_pompeiuFDerivIntegrand_eq (α : ℂ → ℂ) (z η : ℂ) :
    ‖pompeiuFDerivIntegrand α z η‖ = ‖η⁻¹‖ * ‖fderiv ℝ α (η + z)‖ := by
  unfold pompeiuFDerivIntegrand
  rw [norm_smul]

/-! ## Section 2: HasFDerivAt for the translated integral -/

/-- **Pointwise differentiation under the integral sign.** For each
fixed `η : ℂ`, the integrand `z ↦ α (η + z) * η⁻¹` is `ℝ`-differentiable
at every `z`, with derivative `pompeiuFDerivIntegrand α z η`. -/
private lemma hasFDerivAt_translated_integrand_fderiv
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (η z : ℂ) :
    HasFDerivAt (fun w : ℂ => α (η + w) * η⁻¹)
      (pompeiuFDerivIntegrand α z η) z := by
  have h_shift : HasFDerivAt (fun w : ℂ => η + w) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_add η
  have h_α : HasFDerivAt α (fderiv ℝ α (η + z)) (η + z) :=
    (h_smooth.differentiable (by norm_num) _).hasFDerivAt
  have h_comp : HasFDerivAt
      (fun w : ℂ => α (η + w))
      ((fderiv ℝ α (η + z)).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    h_α.comp z h_shift
  have h_comp_simp : HasFDerivAt
      (fun w : ℂ => α (η + w))
      (fderiv ℝ α (η + z)) z := by
    have h_id : (fderiv ℝ α (η + z)).comp (ContinuousLinearMap.id ℝ ℂ)
        = fderiv ℝ α (η + z) := ContinuousLinearMap.comp_id _
    rw [h_id] at h_comp
    exact h_comp
  have h_mul := h_comp_simp.mul_const η⁻¹
  -- h_mul : HasFDerivAt (fun w => α (η + w) * η⁻¹) ((η⁻¹ : ℂ) • fderiv ℝ α (η + z)) z
  exact h_mul

/-- **Geometric inclusion for the complex-parameter path.** If
`‖η‖ > R + ‖z₀‖ + 1` and `z ∈ ball z₀ 1`, then `‖η + z‖ > R`. -/
private lemma norm_path_complex_gt_R_of_outside
    (R : ℝ) (z₀ η z : ℂ)
    (h_norm_η : R + ‖z₀‖ + 1 < ‖η‖) (h_z : z ∈ Metric.ball z₀ 1) :
    R < ‖η + z‖ := by
  have h_dist : ‖z - z₀‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at h_z
    exact h_z
  have h_z_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have : ‖z‖ = ‖z - z₀ + z₀‖ := by ring_nf
    rw [this]
    exact (norm_add_le _ _).trans (by linarith)
  have h_tri : ‖η‖ ≤ ‖η + z‖ + ‖z‖ := by
    have h_eq : (η + z) - z = η := by ring
    have h_step : ‖(η + z) - z‖ ≤ ‖η + z‖ + ‖z‖ := norm_sub_le _ _
    rw [h_eq] at h_step
    exact h_step
  linarith

/-- **HasFDerivAt for the translated parametric integral.** The map
`z ↦ ∫ η, α (η + z) * η⁻¹ ∂vol` is `ℝ`-differentiable at every `z₀`,
with derivative `∫ η, pompeiuFDerivIntegrand α z₀ η ∂vol`. -/
theorem hasFDerivAt_translated_integral
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z₀ : ℂ) :
    HasFDerivAt
      (fun z : ℂ => ∫ η, α (η + z) * η⁻¹ ∂(volume : Measure ℂ))
      (∫ η, pompeiuFDerivIntegrand α z₀ η ∂(volume : Measure ℂ))
      z₀ := by
  -- Setup constants from Chip 2c-prep.
  obtain ⟨M', hM'_nn, hM'⟩ := exists_fderiv_norm_bound h_smooth h_supp
  obtain ⟨R, hR_subset⟩ := h_supp.isBounded.subset_closedBall (0 : ℂ)
  -- Local parameter neighborhood.
  let s : Set ℂ := Metric.ball (z₀ : ℂ) 1
  have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ (by norm_num)
  -- Uniform compact for the bound.
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (R + ‖z₀‖ + 1)
  let bound : ℂ → ℝ := K.indicator (fun η : ℂ => M' * ‖η‖⁻¹)
  -- Define F and F'.
  let F : ℂ → ℂ → ℂ := fun z η => α (η + z) * η⁻¹
  let F' : ℂ → ℂ → (ℂ →L[ℝ] ℂ) := fun z η => pompeiuFDerivIntegrand α z η
  -- Hypothesis: hF_meas — F z is AE strongly measurable, for z in a nbhd of z₀.
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (F z) (volume : Measure ℂ) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    have h_shift : Measurable (fun η : ℂ => η + z) :=
      measurable_id.add_const _
    have h_meas_α : Measurable (fun η : ℂ => α (η + z)) :=
      h_smooth.continuous.measurable.comp h_shift
    have h_meas_inv : Measurable (fun η : ℂ => η⁻¹) := measurable_id.inv
    exact (h_meas_α.mul h_meas_inv).aestronglyMeasurable
  -- Hypothesis: hF_int — F z₀ is integrable.
  have hF_int : Integrable (F z₀) (volume : Measure ℂ) := by
    have h_eq : F z₀ = fun η : ℂ => α (η + z₀) * η⁻¹ := rfl
    rw [h_eq]
    exact integrable_translated_pompeiuIntegrand_of_continuous_hasCompactSupport
      h_smooth.continuous h_supp z₀
  -- Hypothesis: hF'_meas — F' z₀ is AE strongly measurable.
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume : Measure ℂ) := by
    -- F' z₀ η = (η⁻¹ : ℂ) • fderiv ℝ α (η + z₀)
    have h_fderiv_cont : Continuous (fderiv ℝ α) :=
      h_smooth.continuous_fderiv (by norm_num)
    have h_shift : Continuous (fun η : ℂ => η + z₀) :=
      continuous_id.add continuous_const
    have h_fderiv_shift : Continuous (fun η : ℂ => fderiv ℝ α (η + z₀)) :=
      h_fderiv_cont.comp h_shift
    have h_inv : Measurable (fun η : ℂ => (η⁻¹ : ℂ)) := measurable_id.inv
    -- Strong measurability of the scalar.
    have h_inv_sm : AEStronglyMeasurable (fun η : ℂ => (η⁻¹ : ℂ))
        (volume : Measure ℂ) :=
      h_inv.aestronglyMeasurable
    -- Strong measurability of the CLM.
    have h_fderiv_sm : AEStronglyMeasurable
        (fun η : ℂ => fderiv ℝ α (η + z₀)) (volume : Measure ℂ) :=
      h_fderiv_shift.aestronglyMeasurable
    -- Combine via the bilinear scalar action.
    have h_eq : F' z₀ = fun η : ℂ => (η⁻¹ : ℂ) • fderiv ℝ α (η + z₀) := rfl
    rw [h_eq]
    exact h_inv_sm.smul h_fderiv_sm
  -- Hypothesis: h_bound — uniform pointwise bound on s.
  have h_bound : ∀ᵐ η ∂(volume : Measure ℂ), ∀ z ∈ s, ‖F' z η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall (fun η z hz => ?_)
    by_cases hη : η ∈ K
    · -- Inside K: use M' · ‖η‖⁻¹.
      have h_indicator : bound η = M' * ‖η‖⁻¹ := Set.indicator_of_mem hη _
      show ‖F' z η‖ ≤ bound η
      rw [h_indicator, norm_pompeiuFDerivIntegrand_eq, norm_inv]
      have h_bound_fderiv : ‖fderiv ℝ α (η + z)‖ ≤ M' := hM' _
      -- ‖η‖⁻¹ * ‖fderiv ℝ α (η + z)‖ ≤ M' * ‖η‖⁻¹
      have : ‖η‖⁻¹ * ‖fderiv ℝ α (η + z)‖ ≤ ‖η‖⁻¹ * M' :=
        mul_le_mul_of_nonneg_left h_bound_fderiv (inv_nonneg.mpr (norm_nonneg _))
      linarith [this, mul_comm M' (‖η‖⁻¹)]
    · -- Outside K: fderiv ℝ α (η + z) = 0, so F' z η = 0.
      have h_indicator : bound η = 0 := Set.indicator_of_notMem hη _
      have h_norm_η : R + ‖z₀‖ + 1 < ‖η‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hη
        exact lt_of_not_ge hη
      have h_path_norm : R < ‖η + z‖ :=
        norm_path_complex_gt_R_of_outside R z₀ η z h_norm_η hz
      have h_notMem : (η + z) ∉ tsupport α := by
        intro h_in
        have h_le_R := hR_subset h_in
        rw [Metric.mem_closedBall, dist_zero_right] at h_le_R
        linarith
      have h_fderiv_zero : fderiv ℝ α (η + z) = 0 :=
        fderiv_of_notMem_tsupport ℝ h_notMem
      show ‖F' z η‖ ≤ bound η
      rw [h_indicator]
      have h_F'_zero : F' z η = 0 := by
        show pompeiuFDerivIntegrand α z η = 0
        unfold pompeiuFDerivIntegrand
        rw [h_fderiv_zero, smul_zero]
      rw [h_F'_zero, norm_zero]
  -- Hypothesis: bound_integrable.
  have h_bound_int : Integrable bound (volume : Measure ℂ) := by
    have h_int_inv : IntegrableOn (fun η : ℂ => ‖η‖⁻¹) K (volume : Measure ℂ) :=
      integrableOn_inv_norm_closedBall (R + ‖z₀‖ + 1)
    have h_int_scaled :
        IntegrableOn (fun η : ℂ => M' * ‖η‖⁻¹) K (volume : Measure ℂ) :=
      h_int_inv.const_mul M'
    exact h_int_scaled.integrable_indicator Metric.isClosed_closedBall.measurableSet
  -- Hypothesis: h_diff.
  have h_diff : ∀ᵐ η ∂(volume : Measure ℂ), ∀ z ∈ s,
      HasFDerivAt (F · η) (F' z η) z := by
    refine Filter.Eventually.of_forall (fun η z _hz => ?_)
    show HasFDerivAt (fun w : ℂ => α (η + w) * η⁻¹)
      (pompeiuFDerivIntegrand α z η) z
    exact hasFDerivAt_translated_integrand_fderiv h_smooth η z
  -- Apply the parametric integral fderiv theorem.
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := (volume : Measure ℂ)) (F := F) (x₀ := z₀) (s := s)
    (bound := bound) hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff

/-! ## Section 3: Integrability of `pompeiuFDerivIntegrand` -/

/-- The CLM-valued integrand `pompeiuFDerivIntegrand α z₀ η` is integrable
in `η` against `volume`. This is needed to apply
`ContinuousLinearMap.integral_apply`. -/
theorem integrable_pompeiuFDerivIntegrand
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z₀ : ℂ) :
    Integrable (fun η => pompeiuFDerivIntegrand α z₀ η)
      (volume : Measure ℂ) := by
  obtain ⟨M', hM'_nn, hM'⟩ := exists_fderiv_norm_bound h_smooth h_supp
  obtain ⟨R, hR_subset⟩ := h_supp.isBounded.subset_closedBall (0 : ℂ)
  -- The dominating function: K.indicator (M' * ‖η‖⁻¹) with
  -- K = closedBall 0 (R + ‖z₀‖).
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (R + ‖z₀‖)
  let bound : ℂ → ℝ := K.indicator (fun η => M' * ‖η‖⁻¹)
  -- AE strong measurability.
  have h_fderiv_cont : Continuous (fderiv ℝ α) :=
    h_smooth.continuous_fderiv (by norm_num)
  have h_shift : Continuous (fun η : ℂ => η + z₀) :=
    continuous_id.add continuous_const
  have h_fderiv_shift : Continuous (fun η : ℂ => fderiv ℝ α (η + z₀)) :=
    h_fderiv_cont.comp h_shift
  have h_inv : Measurable (fun η : ℂ => (η⁻¹ : ℂ)) := measurable_id.inv
  have h_meas : AEStronglyMeasurable
      (fun η => pompeiuFDerivIntegrand α z₀ η) (volume : Measure ℂ) := by
    have h_eq : (fun η => pompeiuFDerivIntegrand α z₀ η)
        = fun η : ℂ => (η⁻¹ : ℂ) • fderiv ℝ α (η + z₀) := rfl
    rw [h_eq]
    exact h_inv.aestronglyMeasurable.smul h_fderiv_shift.aestronglyMeasurable
  -- Pointwise bound.
  have h_pw : ∀ᵐ η ∂(volume : Measure ℂ),
      ‖pompeiuFDerivIntegrand α z₀ η‖ ≤ bound η := by
    refine Filter.Eventually.of_forall (fun η => ?_)
    by_cases hη : η ∈ K
    · have h_ind : bound η = M' * ‖η‖⁻¹ := Set.indicator_of_mem hη _
      rw [h_ind, norm_pompeiuFDerivIntegrand_eq, norm_inv]
      have h_bound_fderiv : ‖fderiv ℝ α (η + z₀)‖ ≤ M' := hM' _
      have : ‖η‖⁻¹ * ‖fderiv ℝ α (η + z₀)‖ ≤ ‖η‖⁻¹ * M' :=
        mul_le_mul_of_nonneg_left h_bound_fderiv (inv_nonneg.mpr (norm_nonneg _))
      linarith [this, mul_comm M' (‖η‖⁻¹)]
    · have h_ind : bound η = 0 := Set.indicator_of_notMem hη _
      have h_norm_η : R + ‖z₀‖ < ‖η‖ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hη
        exact lt_of_not_ge hη
      have h_norm_path : R < ‖η + z₀‖ := by
        have h_tri : ‖η‖ ≤ ‖η + z₀‖ + ‖z₀‖ := by
          have h_eq : (η + z₀) - z₀ = η := by ring
          have h_step : ‖(η + z₀) - z₀‖ ≤ ‖η + z₀‖ + ‖z₀‖ := norm_sub_le _ _
          rw [h_eq] at h_step
          exact h_step
        linarith
      have h_notMem : (η + z₀) ∉ tsupport α := by
        intro h_in
        have h_le_R := hR_subset h_in
        rw [Metric.mem_closedBall, dist_zero_right] at h_le_R
        linarith
      have h_fderiv_zero : fderiv ℝ α (η + z₀) = 0 :=
        fderiv_of_notMem_tsupport ℝ h_notMem
      rw [h_ind]
      have h_F'_zero : pompeiuFDerivIntegrand α z₀ η = 0 := by
        unfold pompeiuFDerivIntegrand
        rw [h_fderiv_zero, smul_zero]
      rw [h_F'_zero, norm_zero]
  -- Integrability of the dominating function.
  have h_bound_int : Integrable bound (volume : Measure ℂ) := by
    have h_int_inv : IntegrableOn (fun η : ℂ => ‖η‖⁻¹) K (volume : Measure ℂ) :=
      integrableOn_inv_norm_closedBall (R + ‖z₀‖)
    have h_int_scaled :
        IntegrableOn (fun η : ℂ => M' * ‖η‖⁻¹) K (volume : Measure ℂ) :=
      h_int_inv.const_mul M'
    exact h_int_scaled.integrable_indicator Metric.isClosed_closedBall.measurableSet
  -- Combine via Integrable.mono with the bound.
  exact h_bound_int.mono' h_meas h_pw

/-! ## Section 4: HasFDerivAt for `pompeiuKernel α` -/

/-- **HasFDerivAt for `pompeiuKernel α`.** Scale the translated integral
HasFDerivAt by `-(π⁻¹)` and identify with `pompeiuKernel α` via Chip 2a. -/
theorem hasFDerivAt_pompeiuKernel
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z₀ : ℂ) :
    HasFDerivAt (pompeiuKernel α)
      ((-((Real.pi : ℂ)⁻¹) : ℂ) •
        ∫ η, pompeiuFDerivIntegrand α z₀ η ∂(volume : Measure ℂ))
      z₀ := by
  have h_int := hasFDerivAt_translated_integral h_smooth h_supp z₀
  have h_scaled := h_int.const_mul (-((Real.pi : ℂ)⁻¹))
  -- h_scaled : HasFDerivAt (fun z => -π⁻¹ * (∫ η, α (η + z) * η⁻¹))
  --                       (-π⁻¹ • ∫ η, F' z₀ η) z₀
  have h_eq : (fun z : ℂ =>
      -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z) * η⁻¹ ∂(volume : Measure ℂ))
      = pompeiuKernel α := by
    funext z
    exact (pompeiuKernel_eq_translated_integrand α z).symm
  rw [h_eq] at h_scaled
  exact h_scaled

/-! ## Section 5: fderiv identification

`fderiv ℝ (pompeiuKernel α) z₀ v = pompeiuKernel (αDeriv α v) z₀`.

The pointwise application of the integrated CLM is moved into the integral
via `ContinuousLinearMap.integral_apply`, and the resulting scalar integral
is matched back to `pompeiuKernel (αDeriv α v)` via Chip 2a. -/

/-- The bundled CLM-valued integral applied at `v` equals the scalar
integral with `v` plugged into each integrand. -/
private lemma integral_pompeiuFDerivIntegrand_apply
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z₀ v : ℂ) :
    (∫ η, pompeiuFDerivIntegrand α z₀ η ∂(volume : Measure ℂ)) v
      = ∫ η, η⁻¹ * (fderiv ℝ α (η + z₀)) v ∂(volume : Measure ℂ) := by
  have h_int : Integrable (fun η => pompeiuFDerivIntegrand α z₀ η)
      (volume : Measure ℂ) :=
    integrable_pompeiuFDerivIntegrand h_smooth h_supp z₀
  have h_apply := ContinuousLinearMap.integral_apply h_int v
  rw [h_apply]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun η => ?_)
  exact pompeiuFDerivIntegrand_apply α z₀ η v

/-- **fderiv identification.** The fderiv of `pompeiuKernel α` at `z₀`
applied to `v` equals `pompeiuKernel (αDeriv α v) z₀`. This is the
inductive engine: each derivative of `pompeiuKernel α` is a
`pompeiuKernel` of a directional derivative of `α`. -/
theorem fderiv_pompeiuKernel_apply
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z₀ v : ℂ) :
    fderiv ℝ (pompeiuKernel α) z₀ v = pompeiuKernel (αDeriv α v) z₀ := by
  have h_fderiv : fderiv ℝ (pompeiuKernel α) z₀
      = (-((Real.pi : ℂ)⁻¹) : ℂ) •
        ∫ η, pompeiuFDerivIntegrand α z₀ η ∂(volume : Measure ℂ) :=
    (hasFDerivAt_pompeiuKernel h_smooth h_supp z₀).fderiv
  rw [h_fderiv]
  -- LHS: (-π⁻¹ • ∫ η, F' z₀ η) v
  --    = -π⁻¹ • ((∫ η, F' z₀ η) v)
  --    = -π⁻¹ * ((∫ η, F' z₀ η) v)
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [integral_pompeiuFDerivIntegrand_apply h_smooth h_supp z₀ v]
  -- Now: -π⁻¹ * ∫ η, η⁻¹ * (fderiv ℝ α (η + z₀)) v
  -- pompeiuKernel (αDeriv α v) z₀ = -π⁻¹ * ∫ η, αDeriv α v (η + z₀) * η⁻¹
  --                              = -π⁻¹ * ∫ η, (fderiv ℝ α (η + z₀)) v * η⁻¹
  rw [pompeiuKernel_eq_translated_integrand (αDeriv α v) z₀]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun η => ?_)
  show η⁻¹ * (fderiv ℝ α (η + z₀)) v = αDeriv α v (η + z₀) * η⁻¹
  unfold αDeriv
  ring

/-! ## Section 6: Differentiability + fderiv-as-function -/

/-- `pompeiuKernel α` is `ℝ`-differentiable everywhere when `α ∈ C^1` with
compact support. -/
theorem differentiable_pompeiuKernel
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) :
    Differentiable ℝ (pompeiuKernel α) :=
  fun z₀ => (hasFDerivAt_pompeiuKernel h_smooth h_supp z₀).differentiableAt

/-- The function `z ↦ fderiv ℝ (pompeiuKernel α) z v` equals
`pompeiuKernel (αDeriv α v)`. -/
theorem fderiv_pompeiuKernel_apply_eq
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (v : ℂ) :
    (fun z => fderiv ℝ (pompeiuKernel α) z v) = pompeiuKernel (αDeriv α v) := by
  funext z₀
  exact fderiv_pompeiuKernel_apply h_smooth h_supp z₀ v

/-! ## Section 7: `αDeriv α v` smoothness lift -/

/-- For `α ∈ C^(n+1)` with compact support and `v : ℂ`, the directional
derivative `αDeriv α v` is `C^n` with compact support. -/
theorem contDiff_αDeriv {α : ℂ → ℂ} {n : ℕ}
    (h_smooth : ContDiff ℝ (n + 1) α) (v : ℂ) :
    ContDiff ℝ n (αDeriv α v) := by
  -- fderiv ℝ α : ℂ → (ℂ →L[ℝ] ℂ) is C^n by contDiff_succ_iff_fderiv.
  have h_fderiv_contDiff : ContDiff ℝ n (fderiv ℝ α) := by
    have h := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := α)).mp (by
      have : ((n : WithTop ℕ∞) + 1) = ((n + 1 : ℕ) : WithTop ℕ∞) := by
        push_cast; rfl
      rw [this]; exact h_smooth)
    exact h.2.2
  -- αDeriv α v = (fun L => L v) ∘ (fderiv ℝ α). Apply-at-v CLM is C^∞.
  have h_apply_contDiff : ContDiff ℝ n (fun L : ℂ →L[ℝ] ℂ => L v) :=
    (ContinuousLinearMap.apply ℝ ℂ v).contDiff
  have h_comp : ContDiff ℝ n ((fun L : ℂ →L[ℝ] ℂ => L v) ∘ fderiv ℝ α) :=
    h_apply_contDiff.comp h_fderiv_contDiff
  exact h_comp

/-! ## Section 8: ContDiff induction on `n : ℕ` -/

/-- **Chip 2d core induction.** For each natural `n`, `α : ℂ → ℂ` with
`α ∈ C^n` and compact support, `pompeiuKernel α ∈ C^n`. -/
theorem contDiff_pompeiuKernel_of_nat :
    ∀ (n : ℕ) {α : ℂ → ℂ}, ContDiff ℝ n α → HasCompactSupport α →
      ContDiff ℝ n (pompeiuKernel α) := by
  intro n
  induction n with
  | zero =>
    intro α h_smooth h_supp
    -- ContDiff ℝ 0 = Continuous (Chip 2b).
    rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero] at h_smooth ⊢
    exact continuous_pompeiuKernel_of_continuous_hasCompactSupport h_smooth h_supp
  | succ k ih =>
    intro α h_smooth h_supp
    -- Goal: ContDiff ℝ (k+1) (pompeiuKernel α).
    -- Use contDiff_succ_iff_fderiv_apply (since ℂ is finite-dim over ℝ).
    have h_cast : ((k + 1 : ℕ) : WithTop ℕ∞) = ((k : WithTop ℕ∞) + 1) := by
      push_cast; rfl
    rw [h_cast]
    rw [contDiff_succ_iff_fderiv_apply]
    refine ⟨?_, ?_, ?_⟩
    · -- Differentiability.
      have h_smooth_one : ContDiff ℝ 1 α := by
        have h_le : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
          rw [h_cast]
          have : (1 : WithTop ℕ∞) ≤ ((k : WithTop ℕ∞) + 1) :=
            le_add_self
          exact this
        exact h_smooth.of_le h_le
      exact differentiable_pompeiuKernel h_smooth_one h_supp
    · -- n = ω → AnalyticOnNhd: vacuous since k : ℕ is not ω.
      intro h_eq
      exfalso
      -- (k : WithTop ℕ∞) ≠ ω because k is a natural number.
      -- ω = (⊤ : WithTop ℕ∞), and (k : WithTop ℕ∞) = ((k : ℕ∞) : WithTop ℕ∞).
      have h_cast2 : ((k : ℕ) : WithTop ℕ∞) = ((k : ℕ∞) : WithTop ℕ∞) := by
        push_cast; rfl
      rw [h_cast2] at h_eq
      exact WithTop.coe_ne_top h_eq
    · -- For each v, ContDiff ℝ k (fun z => fderiv ℝ (pompeiuKernel α) z v)
      --     = ContDiff ℝ k (pompeiuKernel (αDeriv α v))
      --   by fderiv_pompeiuKernel_apply_eq.
      intro v
      have h_smooth_one : ContDiff ℝ 1 α := by
        have h_le : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
          rw [h_cast]
          exact le_add_self
        exact h_smooth.of_le h_le
      have h_rw : (fun z => fderiv ℝ (pompeiuKernel α) z v)
          = pompeiuKernel (αDeriv α v) :=
        fderiv_pompeiuKernel_apply_eq h_smooth_one h_supp v
      rw [h_rw]
      -- αDeriv α v : ContDiff ℝ k, with compact support.
      have h_αDeriv_smooth : ContDiff ℝ k (αDeriv α v) :=
        contDiff_αDeriv (n := k) h_smooth v
      have h_αDeriv_supp : HasCompactSupport (αDeriv α v) :=
        αDeriv_hasCompactSupport h_supp v
      exact ih h_αDeriv_smooth h_αDeriv_supp

/-! ## Section 9: C^∞ corollary -/

/-- **Chip 2d main theorem — `pompeiuKernel α` is `C^∞`.** For
`α : ℂ → ℂ` of class `C^∞` with compact support, the Pompeiu kernel
`pompeiuKernel α : ℂ → ℂ` is `ℝ`-`C^∞`. -/
theorem contDiff_pompeiuKernel_infty
    {α : ℂ → ℂ} (h_smooth : ContDiff ℝ ∞ α) (h_supp : HasCompactSupport α) :
    ContDiff ℝ ∞ (pompeiuKernel α) := by
  rw [contDiff_infty]
  intro n
  have h_α_n : ContDiff ℝ (n : WithTop ℕ∞) α := h_smooth.of_le (by
    have : (n : WithTop ℕ∞) ≤ ∞ := by
      exact_mod_cast le_top
    exact this)
  exact contDiff_pompeiuKernel_of_nat n h_α_n h_supp

end JacobianChallenge.PompeiuKernel

end
