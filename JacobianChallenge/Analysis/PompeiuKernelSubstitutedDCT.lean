/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Bounded
import JacobianChallenge.Analysis.PompeiuIntegrandIntegrability
import JacobianChallenge.Analysis.PompeiuKernelDCTLimit
import JacobianChallenge.Analysis.PompeiuKernelRadialIntegralFinal
import JacobianChallenge.Analysis.PompeiuKernelRadialSubstitution

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3d-3: DCT on substituted integral

The second-summand DCT limit at the unit scale after substitution:

```
Tendsto (fun ε ↦ ∫ w, α(z + ε·w) · (partialZBar unitRadialBumpC w / w))
  (𝓝[>] 0)
  (𝓝 (α z * (-π))).
```

Combined with Chip 3c-F-3d-2c's negation `-∫ ...`, the limit of the
**second summand** (i.e. `∫ α · ∂̄(regInvSubRadial z ε)`) is
`α z · π`. Together with Chip 3c-F-3c's first-summand limit
`-π · pompeiuKernel(∂̄α) z`, Chip 3c-F-4 concludes
`pompeiuKernel(∂̄α) z = α z`.

Proof structure:

* Establish `Continuous unitRadialBumpC` and `HasCompactSupport
  unitRadialBumpC` (the explicit radial bump from Chip 3c-F-1 is
  smooth and vanishes outside `ball 0 1`).
* Lift to `Continuous (partialZBar unitRadialBumpC)` and
  `HasCompactSupport (partialZBar unitRadialBumpC)` via Chip 3c-E
  helpers `partialZBar_continuous` / `partialZBar_hasCompactSupport`.
* Integrability of `fun w => partialZBar unitRadialBumpC w / w` via
  Chip 1c's `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`
  applied at `z := 0` (since `pompeiuIntegrand g 0 w = g w · w⁻¹ = g w / w`).
* DCT: `tendsto_integral_filter_of_dominated_convergence` with dominator
  `M · ‖partialZBar unitRadialBumpC w / w‖` (M = sup |α|), pointwise
  convergence `α(z + ε·w) → α(z)` from continuity of `α` at `z`.

All sorry-free, axiom-free. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

/-! ## `unitRadialBumpC` properties: smoothness and compact support -/

/-- `unitRadialBumpC` is `ContDiff ℝ n` for all `n` (composition of the smooth
`radialBump 0 1` with `Complex.ofRealCLM`). -/
lemma unitRadialBumpC_contDiff {n : ℕ∞} : ContDiff ℝ n unitRadialBumpC := by
  have h_real : ContDiff ℝ n (radialBump 0 1) := radialBump_contDiff 0 one_pos
  exact Complex.ofRealCLM.contDiff.comp h_real

/-- `unitRadialBumpC` is continuous. -/
lemma unitRadialBumpC_continuous : Continuous unitRadialBumpC :=
  (unitRadialBumpC_contDiff (n := 0)).continuous

/-- `unitRadialBumpC w = 0` outside `ball 0 1`. -/
lemma unitRadialBumpC_eq_zero_of_not_mem_ball
    {w : ℂ} (hw : w ∉ Metric.ball (0 : ℂ) 1) :
    unitRadialBumpC w = 0 := by
  show ((radialBump 0 1 w : ℝ) : ℂ) = 0
  rw [radialBump_eq_zero_of_not_mem_ball 0 one_pos hw]
  norm_num

/-- The support of `unitRadialBumpC` is contained in `closedBall 0 1`. -/
lemma tsupport_unitRadialBumpC_subset :
    tsupport unitRadialBumpC ⊆ Metric.closedBall (0 : ℂ) 1 := by
  -- `support ⊆ ball 0 1` (anything outside ball is mapped to 0).
  have h_supp : Function.support unitRadialBumpC ⊆ Metric.ball 0 1 := by
    intro w hw
    by_contra hw_not
    exact hw (unitRadialBumpC_eq_zero_of_not_mem_ball hw_not)
  -- `tsupport = closure support ⊆ closure (ball 0 1) ⊆ closedBall 0 1`.
  refine (closure_mono h_supp).trans ?_
  exact Metric.closure_ball_subset_closedBall

/-- `unitRadialBumpC` has compact support. -/
lemma unitRadialBumpC_hasCompactSupport : HasCompactSupport unitRadialBumpC :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset (isClosed_tsupport _)
    tsupport_unitRadialBumpC_subset

/-! ## `partialZBar unitRadialBumpC` properties -/

/-- `partialZBar unitRadialBumpC` is continuous. -/
lemma partialZBar_unitRadialBumpC_continuous :
    Continuous (partialZBar unitRadialBumpC) :=
  partialZBar_continuous (unitRadialBumpC_contDiff (n := 1))

/-- `partialZBar unitRadialBumpC` has compact support. -/
lemma partialZBar_unitRadialBumpC_hasCompactSupport :
    HasCompactSupport (partialZBar unitRadialBumpC) :=
  partialZBar_hasCompactSupport unitRadialBumpC_hasCompactSupport

/-! ## Integrability of `∂̄(unitRadialBumpC)(w) / w` -/

/-- The function `w ↦ partialZBar unitRadialBumpC w / w` is `Bochner`-integrable
on `ℂ`. Applies Chip 1c's `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`
at `z := 0`, since `pompeiuIntegrand g 0 w = g w · w⁻¹ = g w / w`. -/
lemma integrable_partialZBar_unitRadialBumpC_div :
    Integrable (fun w : ℂ => partialZBar unitRadialBumpC w / w) := by
  have h_int :
      Integrable (pompeiuIntegrand (partialZBar unitRadialBumpC) (0 : ℂ)) :=
    integrable_pompeiuIntegrand_of_continuous_hasCompactSupport
      partialZBar_unitRadialBumpC_continuous
      partialZBar_unitRadialBumpC_hasCompactSupport 0
  convert h_int using 1
  funext w
  show partialZBar unitRadialBumpC w / w
      = partialZBar unitRadialBumpC w * (w - 0)⁻¹
  rw [sub_zero, div_eq_mul_inv]

/-- Integrability of the dominator `M · ‖∂̄(unitRadialBumpC)(w) / w‖`. -/
lemma integrable_dominator_substituted (M : ℝ) :
    Integrable (fun w : ℂ => M * ‖partialZBar unitRadialBumpC w / w‖) := by
  exact (integrable_partialZBar_unitRadialBumpC_div.norm).const_mul M

/-! ## Pointwise convergence: `α(z + ε·w) → α(z)` as `ε → 0⁺` -/

/-- For continuous `α : ℂ → ℂ` and any `z, w : ℂ`,
`α(z + (ε:ℂ) · w) → α(z)` as `ε → 0⁺`. -/
lemma tendsto_alpha_at_substituted {α : ℂ → ℂ} (h_cont : Continuous α)
    (z w : ℂ) :
    Tendsto (fun ε : ℝ => α (z + (ε : ℂ) * w)) (𝓝[>] (0 : ℝ)) (𝓝 (α z)) := by
  -- ε ↦ (ε : ℂ) * w is continuous (= z + tail tendsto 0 as ε → 0).
  have h_aux : Tendsto (fun ε : ℝ => z + (ε : ℂ) * w) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have h_eps : Tendsto (fun ε : ℝ => (ε : ℂ) * w) (𝓝 (0 : ℝ)) (𝓝 (0 * w)) := by
      have h_ofReal : Tendsto (fun ε : ℝ => (ε : ℂ))
          (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt
      exact h_ofReal.mul_const w
    simp only [zero_mul] at h_eps
    have h_add : Tendsto (fun ε : ℝ => z + (ε : ℂ) * w)
        (𝓝 (0 : ℝ)) (𝓝 (z + 0)) :=
      (tendsto_const_nhds.add h_eps)
    simp only [add_zero] at h_add
    exact h_add.mono_left nhdsWithin_le_nhds
  exact (h_cont.tendsto z).comp h_aux

/-! ## Main DCT theorem -/

/-- **Chip 3c-F-3d-3 — DCT on the substituted integral.** As `ε → 0⁺`,

```
∫ w : ℂ, α(z + ε·w) · (partialZBar unitRadialBumpC w / w)
  → α(z) · (-π).
```

Proof: mathlib's `tendsto_integral_filter_of_dominated_convergence` with
dominator `M · ‖partialZBar unitRadialBumpC w / w‖` (M = sup |α| from
`Continuous.bounded_above_of_compact_support`), integrable by
`integrable_partialZBar_unitRadialBumpC_div`. Pointwise: `α(z + ε·w) → α(z)`
from continuity of `α`; multiplying by the constant
`partialZBar unitRadialBumpC w / w` gives the integrand limit. Then
`integral_const_mul` plus Chip 3c-F-2-final
(`integral_partialZBar_unitRadialBumpC_div_eq_neg_pi`) close the limit
value. -/
theorem tendsto_integral_alpha_substituted
    {α : ℂ → ℂ} (h_cont : Continuous α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Tendsto (fun ε : ℝ =>
        ∫ w : ℂ, α (z + (ε : ℂ) * w) *
          (partialZBar unitRadialBumpC w / w))
      (𝓝[>] (0 : ℝ))
      (𝓝 (α z * ((-Real.pi : ℝ) : ℂ))) := by
  -- Sup bound on |α|.
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support h_cont h_supp
  -- DCT applied to the family `f_ε(w) := α(z + ε·w) · ∂̄(unitRadialBumpC)(w) / w`.
  have h_limit_form :
      Tendsto (fun ε : ℝ =>
          ∫ w : ℂ, α (z + (ε : ℂ) * w) *
            (partialZBar unitRadialBumpC w / w))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ w : ℂ, α z *
              (partialZBar unitRadialBumpC w / w))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun w => M * ‖partialZBar unitRadialBumpC w / w‖) ?_ ?_ ?_ ?_
    · -- AEStronglyMeasurable: integrand factors as continuous ∘ continuous map
      -- times an AEStronglyMeasurable function (∂̄/w, integrable hence
      -- AEStronglyMeasurable).
      filter_upwards [self_mem_nhdsWithin] with ε _hε_pos
      have h_first :
          AEStronglyMeasurable (fun w : ℂ => α (z + (ε : ℂ) * w))
            (volume : Measure ℂ) := by
        refine Continuous.aestronglyMeasurable ?_
        exact h_cont.comp ((continuous_const.add
          ((continuous_const : Continuous (fun _ : ℂ => (ε : ℂ))).mul continuous_id)))
      have h_second :
          AEStronglyMeasurable
            (fun w : ℂ => partialZBar unitRadialBumpC w / w)
            (volume : Measure ℂ) :=
        integrable_partialZBar_unitRadialBumpC_div.aestronglyMeasurable
      exact h_first.mul h_second
    · -- Norm bound for every ε.
      filter_upwards [self_mem_nhdsWithin] with ε _hε_pos
      refine Filter.Eventually.of_forall (fun w => ?_)
      rw [norm_mul]
      have h_α : ‖α (z + (ε : ℂ) * w)‖ ≤ M := hM _
      have h_nn : 0 ≤ ‖partialZBar unitRadialBumpC w / w‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_right h_α h_nn
    · -- Dominator integrability.
      exact integrable_dominator_substituted M
    · -- Pointwise convergence.
      refine Filter.Eventually.of_forall (fun w => ?_)
      exact (tendsto_alpha_at_substituted h_cont z w).mul_const _
  -- Replace the limit integral via `integral_const_mul`.
  have h_int_const :
      (∫ w : ℂ, α z * (partialZBar unitRadialBumpC w / w))
        = α z * ((-Real.pi : ℝ) : ℂ) := by
    have h_pull : (∫ w : ℂ, α z * (partialZBar unitRadialBumpC w / w))
        = α z * ∫ w : ℂ, partialZBar unitRadialBumpC w / w :=
      integral_const_mul (α z) (fun w : ℂ => partialZBar unitRadialBumpC w / w)
    rw [h_pull, integral_partialZBar_unitRadialBumpC_div_eq_neg_pi]
  rw [← h_int_const]
  exact h_limit_form

end JacobianChallenge.PompeiuKernel
