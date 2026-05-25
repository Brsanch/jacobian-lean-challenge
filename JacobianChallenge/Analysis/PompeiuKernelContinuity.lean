/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelTranslation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Chip 2b: continuity of the Pompeiu kernel in `z`

Using Chip 2a's translated form
`pompeiuKernel α z = -(π⁻¹) · ∫ η, α (η + z) · η⁻¹`, the singularity
`η⁻¹` is independent of `z`, so continuity of the parametric integral
follows from dominated convergence with a `z₀`-local uniform bound.

## Main result

* `continuous_pompeiuKernel_of_continuous_hasCompactSupport`:
  if `α : ℂ → ℂ` is continuous with compact support, then
  `pompeiuKernel α : ℂ → ℂ` is continuous.

## Method

For fixed `z₀`, take a compact `K = closedBall 0 (R + ‖z₀‖ + 1)` where
`R` bounds `tsupport α`. For `z ∈ closedBall z₀ 1`:
- `η ∉ K` ⇒ `‖η + z‖ > R` ⇒ `η + z ∉ tsupport α` ⇒ `α (η + z) = 0`,
  so the integrand vanishes.
- `η ∈ K` ⇒ `‖α (η + z) · η⁻¹‖ ≤ M · ‖η‖⁻¹` where `M = ‖α‖_∞`.

The dominating function `K.indicator (fun η => M · ‖η‖⁻¹)` is integrable
(Chip 1b polar bound on `K`, constant-mul, restricted indicator), so
`continuousAt_of_dominated` gives `ContinuousAt (pompeiuKernel α) z₀`.
The conclusion follows from `continuous_iff_continuousAt`.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric
open scoped Real Topology ENNReal

namespace JacobianChallenge.PompeiuKernel

/-! ## Local dominating function for the translated integrand -/

/-- For each `z₀`, there is a uniform dominating function on a
neighborhood of `z₀` for the translated Pompeiu integrand
`η ↦ α (η + z) · η⁻¹`. -/
private lemma exists_translated_continuity_bound_at
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z₀ : ℂ) :
    ∃ (bound : ℂ → ℝ),
      Integrable bound (volume : Measure ℂ) ∧
      ∀ᶠ z in 𝓝 z₀, ∀ᵐ η ∂(volume : Measure ℂ),
        ‖α (η + z) * η⁻¹‖ ≤ bound η := by
  obtain ⟨M, hM⟩ := h_cont.bounded_above_of_compact_support h_supp
  obtain ⟨R, hR⟩ := h_supp.isBounded.subset_closedBall (0 : ℂ)
  -- The uniform compact containing `tsupport α − z` for `z ∈ closedBall z₀ 1`.
  set K := Metric.closedBall (0 : ℂ) (R + ‖z₀‖ + 1) with hK_def
  refine ⟨K.indicator (fun η : ℂ => M * ‖η‖⁻¹), ?_, ?_⟩
  · -- Integrability of `K.indicator (fun η => M · ‖η‖⁻¹)`.
    have h_int_inv : IntegrableOn (fun η : ℂ => ‖η‖⁻¹) K (volume : Measure ℂ) :=
      integrableOn_inv_norm_closedBall (R + ‖z₀‖ + 1)
    have h_int_M : IntegrableOn (fun η : ℂ => M * ‖η‖⁻¹) K (volume : Measure ℂ) :=
      h_int_inv.const_mul M
    exact h_int_M.integrable_indicator Metric.isClosed_closedBall.measurableSet
  · -- Uniform domination on `closedBall z₀ 1` (a neighborhood of `z₀`).
    refine Filter.eventually_of_mem (Metric.closedBall_mem_nhds z₀ zero_lt_one) ?_
    intro z hz
    refine Filter.Eventually.of_forall ?_
    intro η
    by_cases hη : η ∈ K
    · -- Inside `K`: bound by `M · ‖η‖⁻¹`.
      rw [Set.indicator_of_mem hη]
      rw [norm_mul, norm_inv]
      exact mul_le_mul_of_nonneg_right (hM (η + z)) (inv_nonneg.mpr (norm_nonneg _))
    · -- Outside `K`: `‖η‖ > R + ‖z₀‖ + 1`, so `α (η + z) = 0`.
      rw [Set.indicator_of_notMem hη]
      have h_norm_η : R + ‖z₀‖ + 1 < ‖η‖ := by
        have h_not_le := hη
        rw [Metric.mem_closedBall, dist_zero_right] at h_not_le
        exact lt_of_not_ge h_not_le
      have h_norm_z : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have hz_dist : ‖z - z₀‖ ≤ 1 := by
          have := hz
          rw [Metric.mem_closedBall, dist_eq_norm] at this
          exact this
        have h_tri : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
          have h_split : z = (z - z₀) + z₀ := by ring
          nth_rewrite 1 [h_split]
          exact norm_add_le _ _
        linarith
      have h_eta_plus_z_norm : R < ‖η + z‖ := by
        have h_split : ‖η‖ ≤ ‖η + z‖ + ‖z‖ := by
          have h_eq : (η + z) - z = η := by ring
          have h_tri : ‖(η + z) - z‖ ≤ ‖η + z‖ + ‖z‖ := norm_sub_le _ _
          rwa [h_eq] at h_tri
        linarith
      have h_not_in_tsupp : η + z ∉ tsupport α := by
        intro h_in
        have h_le_R := hR h_in
        rw [Metric.mem_closedBall, dist_zero_right] at h_le_R
        linarith
      have h_α_zero : α (η + z) = 0 :=
        image_eq_zero_of_notMem_tsupport h_not_in_tsupp
      simp [h_α_zero]

/-! ## Continuity at a point, via dominated convergence -/

/-- `ContinuousAt` for the parametric integral `z ↦ ∫ η, α (η + z) · η⁻¹`,
obtained via `continuousAt_of_dominated` and the local bound above. -/
private lemma continuousAt_translated_integral
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z₀ : ℂ) :
    ContinuousAt (fun z : ℂ => ∫ η, α (η + z) * η⁻¹) z₀ := by
  obtain ⟨bound, h_int_bound, h_bound⟩ :=
    exists_translated_continuity_bound_at h_cont h_supp z₀
  refine continuousAt_of_dominated ?_ h_bound h_int_bound ?_
  · -- AEStronglyMeasurable of `η ↦ α (η + z) · η⁻¹` for `z` near `z₀`.
    refine Filter.Eventually.of_forall ?_
    intro z
    have h_meas_α_shift : Measurable (fun η : ℂ => α (η + z)) :=
      h_cont.measurable.comp (measurable_id.add_const z)
    have h_meas_inv : Measurable (fun η : ℂ => η⁻¹) := measurable_id.inv
    exact (h_meas_α_shift.mul h_meas_inv).aestronglyMeasurable
  · -- ContinuousAt of `z ↦ α (η + z) · η⁻¹` at `z₀` for ae `η`.
    refine Filter.Eventually.of_forall ?_
    intro η
    refine ContinuousAt.mul ?_ continuousAt_const
    exact (h_cont.continuousAt).comp (continuous_const.add continuous_id).continuousAt

/-! ## Main theorem -/

/-- **Chip 2b — Continuity of `pompeiuKernel α` in `z`.** When `α` is
continuous with compact support, the Pompeiu kernel `pompeiuKernel α`
is continuous as a function of `z`. Proven by applying
`continuousAt_of_dominated` to Chip 2a's translated form (singularity
pinned at `η = 0`), with a `z₀`-local dominating function derived from
Chip 1b's polar bound and boundedness of `α`. -/
theorem continuous_pompeiuKernel_of_continuous_hasCompactSupport
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) :
    Continuous (pompeiuKernel α) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  have h_eq : (fun z : ℂ => pompeiuKernel α z)
      = fun z : ℂ => -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z) * η⁻¹ := by
    funext z
    exact pompeiuKernel_eq_translated_integrand α z
  rw [show pompeiuKernel α = (fun z : ℂ => -((Real.pi : ℂ)⁻¹) * ∫ η, α (η + z) * η⁻¹)
      from h_eq]
  exact (continuousAt_translated_integral h_cont h_supp z₀).const_mul _

end JacobianChallenge.PompeiuKernel

end
