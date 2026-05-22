/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2Sq
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Positive chart-local L²-square seminorm on a non-vanishing ball

If `localCoeff om y` is nowhere-zero on an open ball
`Metric.ball z₀ ε ⊆ (chartAt ℂ y).target` (with `ε > 0`), then the
chart-local L²-square seminorm of `om` on that ball is **strictly
positive**.

Proof: by continuity at `z₀`, there's a smaller ball `Metric.ball z₀ ε'`
on which `‖localCoeff om y z‖ ≥ c := ‖localCoeff om y z₀‖ / 2 > 0`.
Squaring and integrating the constant lower bound:

```
∫⁻ z in ball z₀ ε, ‖localCoeff om y z‖₊² ∂volume
  ≥ ∫⁻ z in ball z₀ ε', ‖localCoeff om y z‖₊² ∂volume      (monotone in set)
  ≥ ∫⁻ z in ball z₀ ε', (ENNReal.ofReal c)² ∂volume         (pointwise lower bound)
  = (ENNReal.ofReal c)² · volume(ball z₀ ε')
  > 0                                                       (c > 0 and volume > 0).
```

This is chip E.3 of the L²-positivity arc. Chip E.4 will combine this
with the partition-of-unity sum to get `0 < globalPettersonL2Sq om f`
for `om ≠ 0`.

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Positive L²-square seminorm on a non-vanishing ball.**

Given an open ball `Metric.ball z₀ ε ⊆ (chartAt ℂ y).target` on which
`localCoeff om y` is everywhere nonzero (with `ε > 0`), the
chart-local L²-square seminorm of `om` on that ball is `> 0`. -/
theorem chartLocalL2Sq_pos_of_ball_nonvanishing
    (om : HolomorphicOneForm X) (y : X)
    {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h_sub : Metric.ball z₀ ε ⊆ (chartAt ℂ y).target)
    (h_ne : ∀ z ∈ Metric.ball z₀ ε, localCoeff om y z ≠ 0) :
    0 < chartLocalL2Sq om y (Metric.ball z₀ ε) := by
  -- z₀ is in the open ball.
  have hz₀_mem : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε
  -- localCoeff om y z₀ ≠ 0 by hypothesis, so its norm > 0.
  have hz₀_ne : localCoeff om y z₀ ≠ 0 := h_ne z₀ hz₀_mem
  have h_pos : 0 < ‖localCoeff om y z₀‖ := norm_pos_iff.mpr hz₀_ne
  -- Threshold c := ‖localCoeff om y z₀‖ / 2 > 0.
  set c : ℝ := ‖localCoeff om y z₀‖ / 2 with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; linarith
  have hc_lt : c < ‖localCoeff om y z₀‖ := by rw [hc_def]; linarith
  -- Continuity of ‖localCoeff om y ·‖ at z₀.
  have h_cont_at_norm : ContinuousAt (fun z => ‖localCoeff om y z‖) z₀ := by
    have h_cont_on : ContinuousOn (localCoeff om y) (chartAt ℂ y).target :=
      (localCoeff_analyticOn om y).continuousOn
    have h_target_mem : z₀ ∈ (chartAt ℂ y).target := h_sub hz₀_mem
    have h_cont_at_lc : ContinuousAt (localCoeff om y) z₀ :=
      (h_cont_on z₀ h_target_mem).continuousAt
        ((chartAt ℂ y).open_target.mem_nhds h_target_mem)
    exact h_cont_at_lc.norm
  -- Get a small radius ε₁ > 0 where ‖localCoeff om y z‖ > c.
  have h_eventually : ∀ᶠ z in 𝓝 z₀, c < ‖localCoeff om y z‖ := by
    have : Set.Ioi c ∈ 𝓝 ‖localCoeff om y z₀‖ := Ioi_mem_nhds hc_lt
    exact h_cont_at_norm.tendsto.eventually this
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ := Metric.eventually_nhds_iff_ball.mp h_eventually
  -- Choose ε' = min(ε₁/2, ε/2): strictly less than both ε and ε₁, positive.
  set ε' : ℝ := min (ε₁ / 2) (ε / 2) with hε'_def
  have hε'_pos : 0 < ε' := by rw [hε'_def]; positivity
  have hε'_lt_ε : ε' < ε := by
    rw [hε'_def]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hε'_lt_ε₁ : ε' < ε₁ := by
    rw [hε'_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h_ball_subset : Metric.ball z₀ ε' ⊆ Metric.ball z₀ ε := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith
  -- On ball z₀ ε' have ENNReal.ofReal c ≤ ‖localCoeff y z‖₊ (ennreal cast).
  have h_lower_bound : ∀ z ∈ Metric.ball z₀ ε',
      (ENNReal.ofReal c)^2 ≤ (‖localCoeff om y z‖₊ : ℝ≥0∞)^2 := by
    intro z hz
    have hz_in_ε₁ : z ∈ Metric.ball z₀ ε₁ := by
      rw [Metric.mem_ball] at hz ⊢; linarith
    have h_gt : c < ‖localCoeff om y z‖ := hε₁ z hz_in_ε₁
    -- ENNReal.ofReal c ≤ ENNReal.ofReal ‖localCoeff om y z‖ = (‖·‖₊ : ℝ≥0∞).
    have h_le : ENNReal.ofReal c ≤ ENNReal.ofReal ‖localCoeff om y z‖ :=
      ENNReal.ofReal_le_ofReal (le_of_lt h_gt)
    have h_eq : ENNReal.ofReal ‖localCoeff om y z‖
        = (‖localCoeff om y z‖₊ : ℝ≥0∞) :=
      (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).trans (by rfl)
    rw [h_eq] at h_le
    exact pow_le_pow_left' h_le 2
  -- Bound the lintegral from below.
  unfold chartLocalL2Sq JacobianChallenge.L2NormSq
  -- Step 1: ∫⁻ z in ball ε, ‖·‖₊² ≥ ∫⁻ z in ball ε', ‖·‖₊² (monotone in set).
  have h_step_set :
      ∫⁻ z in Metric.ball z₀ ε',
          (‖localCoeff om y z‖₊ : ℝ≥0∞)^2 ∂(volume : Measure ℂ)
      ≤ ∫⁻ x, (‖localCoeff om y x‖₊ : ℝ≥0∞)^2
          ∂((volume : Measure ℂ).restrict (Metric.ball z₀ ε)) := by
    show ∫⁻ z in Metric.ball z₀ ε', _ ∂(volume : Measure ℂ)
        ≤ ∫⁻ z in Metric.ball z₀ ε, _ ∂(volume : Measure ℂ)
    exact lintegral_mono_set h_ball_subset
  -- Step 2: ∫⁻ z in ball ε', ‖·‖₊² ≥ ∫⁻ z in ball ε', (ofReal c)² (pointwise bound).
  have h_step_pt :
      ∫⁻ _ in Metric.ball z₀ ε',
          (ENNReal.ofReal c)^2 ∂(volume : Measure ℂ)
      ≤ ∫⁻ z in Metric.ball z₀ ε',
          (‖localCoeff om y z‖₊ : ℝ≥0∞)^2 ∂(volume : Measure ℂ) := by
    refine setLIntegral_mono_ae' Metric.isOpen_ball.measurableSet ?_
    exact Filter.Eventually.of_forall h_lower_bound
  -- Step 3: ∫⁻ in ball ε', constant = constant · volume(ball ε').
  have h_step_const :
      ∫⁻ _ in Metric.ball z₀ ε',
          (ENNReal.ofReal c)^2 ∂(volume : Measure ℂ)
      = (ENNReal.ofReal c)^2 * (volume : Measure ℂ) (Metric.ball z₀ ε') := by
    rw [setLIntegral_const]
  -- Step 4: positivity of the constant times positive volume.
  have h_const_pos : 0 < (ENNReal.ofReal c)^2 := by
    have h_ofReal_pos : 0 < ENNReal.ofReal c := ENNReal.ofReal_pos.mpr hc_pos
    have h_ofReal_ne : (ENNReal.ofReal c) ≠ 0 := h_ofReal_pos.ne'
    have h_sq_ne : (ENNReal.ofReal c)^2 ≠ 0 := pow_ne_zero 2 h_ofReal_ne
    exact h_sq_ne.bot_lt
  have h_vol_pos : 0 < (volume : Measure ℂ) (Metric.ball z₀ ε') :=
    Metric.measure_ball_pos volume z₀ hε'_pos
  have h_mul_pos :
      0 < (ENNReal.ofReal c)^2 * (volume : Measure ℂ) (Metric.ball z₀ ε') :=
    ENNReal.mul_pos h_const_pos.ne' h_vol_pos.ne'
  -- Combine.
  calc 0 < (ENNReal.ofReal c)^2 * (volume : Measure ℂ) (Metric.ball z₀ ε') :=
            h_mul_pos
    _ = ∫⁻ _ in Metric.ball z₀ ε',
            (ENNReal.ofReal c)^2 ∂(volume : Measure ℂ) := h_step_const.symm
    _ ≤ ∫⁻ z in Metric.ball z₀ ε',
            (‖localCoeff om y z‖₊ : ℝ≥0∞)^2 ∂(volume : Measure ℂ) := h_step_pt
    _ ≤ ∫⁻ x, (‖localCoeff om y x‖₊ : ℝ≥0∞)^2
            ∂((volume : Measure ℂ).restrict (Metric.ball z₀ ε)) := h_step_set

end HolomorphicOneForm

end
