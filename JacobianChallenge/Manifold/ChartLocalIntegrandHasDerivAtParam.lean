/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticOnChartLocalIntegrand
import JacobianChallenge.Manifold.ChartLocalIntegrandDerivIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # D2: `HasDerivAt` of the chart-coord parametric integral with value `f z`

For `f : ℂ → ℂ` analytic on a convex open set `S ⊆ ℂ` containing `z₀`,
the parametric integral

  `g(z) := ∫ t in 0..1, f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t`

has `HasDerivAt g (f z) z` for every `z ∈ S`. Combines:

* `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` —
  the parametric Fréchet derivative at `𝕜 = ℂ` (the same machinery
  chip A wraps for `AnalyticOn`), giving
  `HasDerivAt g (∫ t in 0..1, chartLocalIntegrandDerivInZ f z₀ z t) z`;
* D1 (`integral_chartLocalIntegrandDerivInZ_eq`) collapses the integral
  to `f z`.

This is the **D2 sub-atom** of chip D (`ChartLocalPrimitiveFTC`). D3
upgrades the `HasDerivAt` to `mfderiv 𝓘(ℂ) 𝓘(ℂ) g z = smulRight 1 (f z)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology MeasureTheory ContDiff
open MeasureTheory Set Filter

namespace JacobianChallenge

/-- **D2: `HasDerivAt` of the chart-coord parametric integral with value `f z`.**

For `f : ℂ → ℂ` analytic on a convex open set `S` containing `z₀`,
the parametric integral `z ↦ ∫ t in 0..1, f(B(z₀,z,t)) * V(z₀,z,t)`
has ℂ-derivative `f z` at every `z ∈ S`. -/
theorem hasDerivAt_chartLocalIntegrand_param
    {f : ℂ → ℂ} {S : Set ℂ}
    (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    (hf : AnalyticOn ℂ f S)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) {z : ℂ} (hz : z ∈ S) :
    HasDerivAt (fun z' : ℂ => ∫ t in (0 : ℝ)..1,
        f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t)
      (f z) z := by
  -- Assemble the hypotheses for mathlib's parametric Fréchet theorem.
  have hf_cts : ContinuousOn f S := hf.continuousOn
  have hfd_cts : ContinuousOn (deriv f) S := by
    have h_deriv_an : AnalyticOnNhd ℂ (deriv f) S := by
      intro w hw
      exact (hf.analyticAt (hS_open.mem_nhds hw)).deriv
    exact h_deriv_an.continuousOn
  have h_slice_int : ∀ w ∈ S, Continuous (fun t : ℝ =>
      f (bumpedSegment z₀ w t) * chartCoordVelocity z₀ w t) :=
    fun w hw => continuous_chartLocalIntegrand_slice hS_conv hf_cts hz₀ hw
  have h_slice_deriv : ∀ w ∈ S, Continuous (fun t : ℝ =>
      chartLocalIntegrandDerivInZ f z₀ w t) :=
    fun w hw => continuous_chartLocalIntegrandDerivInZ_slice
      hS_conv hf_cts hfd_cts hz₀ hw
  have h_deriv_on_S : ContinuousOn
      (fun p : ℂ × ℝ => chartLocalIntegrandDerivInZ f z₀ p.1 p.2)
      (S ×ˢ Set.univ) :=
    continuousOn_chartLocalIntegrandDerivInZ hS_conv hf_cts hfd_cts hz₀
  -- Local ε-ball + uniform `M`-bound on the deriv, by compactness on
  -- the closed `ε`-ball × `[0, 1]`.
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hS_open z hz
  set ε := δ / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h_ball_sub : Metric.ball z ε ⊆ S := by
    intro w hw
    apply hδ_sub
    rw [Metric.mem_ball] at hw ⊢
    linarith
  have h_cb_sub : Metric.closedBall z ε ⊆ S := by
    intro w hw
    apply hδ_sub
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    linarith
  have h_compact : IsCompact
      (Metric.closedBall z ε ×ˢ Set.Icc (0 : ℝ) 1) :=
    (isCompact_closedBall z ε).prod isCompact_Icc
  have h_ne : (Metric.closedBall z ε ×ˢ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨(z, 0), Metric.mem_closedBall_self (le_of_lt hε_pos),
      by constructor <;> norm_num⟩
  have h_deriv_compact : ContinuousOn
      (fun p : ℂ × ℝ => chartLocalIntegrandDerivInZ f z₀ p.1 p.2)
      (Metric.closedBall z ε ×ˢ Set.Icc (0 : ℝ) 1) := by
    apply h_deriv_on_S.mono
    intro p hp
    exact ⟨h_cb_sub hp.1, mem_univ _⟩
  have h_norm_cts : ContinuousOn
      (fun p : ℂ × ℝ => ‖chartLocalIntegrandDerivInZ f z₀ p.1 p.2‖)
      (Metric.closedBall z ε ×ˢ Set.Icc (0 : ℝ) 1) :=
    h_deriv_compact.norm
  obtain ⟨p_max, _, hp_max⟩ :=
    h_compact.exists_isMaxOn h_ne h_norm_cts
  set M : ℝ := ‖chartLocalIntegrandDerivInZ f z₀ p_max.1 p_max.2‖ with hM_def
  -- Package hypotheses for mathlib's parametric Fréchet theorem.
  have h_ball_nhds : Metric.ball z ε ∈ 𝓝 z := Metric.ball_mem_nhds z hε_pos
  have h_meas_F_nhds : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun t : ℝ =>
          f (bumpedSegment z₀ w t) * chartCoordVelocity z₀ w t)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    have h_S_nhds : S ∈ 𝓝 z := hS_open.mem_nhds hz
    filter_upwards [h_S_nhds] with w hw
    exact (h_slice_int w hw).aestronglyMeasurable.restrict
  have h_int_F_z : IntervalIntegrable
      (fun t : ℝ => f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t)
      volume 0 1 :=
    (h_slice_int z hz).intervalIntegrable 0 1
  have h_meas_F'_z : AEStronglyMeasurable
      (fun t : ℝ => chartLocalIntegrandDerivInZ f z₀ z t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    (h_slice_deriv z hz).aestronglyMeasurable.restrict
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ w ∈ Metric.ball z ε,
        ‖chartLocalIntegrandDerivInZ f z₀ w t‖ ≤ M := by
    refine Filter.Eventually.of_forall ?_
    intro t ht w hw_ball
    have hw_cb : w ∈ Metric.closedBall z ε := by
      rw [Metric.mem_ball] at hw_ball
      rw [Metric.mem_closedBall]
      linarith
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hp_mem : (w, t) ∈ Metric.closedBall z ε ×ˢ Set.Icc (0 : ℝ) 1 :=
      Set.mk_mem_prod hw_cb ht_Icc
    exact hp_max hp_mem
  have h_bound_int : IntervalIntegrable (fun _ : ℝ => M) volume 0 1 :=
    intervalIntegrable_const
  have h_diff_on_ball : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
      ∀ w ∈ Metric.ball z ε, HasDerivAt
        (fun z' : ℂ =>
          f (bumpedSegment z₀ z' t) * chartCoordVelocity z₀ z' t)
        (chartLocalIntegrandDerivInZ f z₀ w t) w := by
    refine Filter.Eventually.of_forall ?_
    intro t _ w hw_ball
    exact hasDerivAt_chartLocalIntegrand_in_z hS_open hS_conv hf hz₀
      (h_ball_sub hw_ball) t
  -- Mathlib parametric Fréchet derivative.
  have h_derivAt :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun z t => f (bumpedSegment z₀ z t) * chartCoordVelocity z₀ z t)
      (F' := fun z t => chartLocalIntegrandDerivInZ f z₀ z t)
      (x₀ := z) (s := Metric.ball z ε) (a := 0) (b := 1) (bound := fun _ => M)
      h_ball_nhds h_meas_F_nhds h_int_F_z h_meas_F'_z
      h_bound h_bound_int h_diff_on_ball
  -- h_derivAt.2 :
  --   HasDerivAt (fun z' => ∫ t in 0..1, f(B(z₀,z',t)) * V(z₀,z',t))
  --              (∫ t in 0..1, chartLocalIntegrandDerivInZ f z₀ z t) z
  -- Collapse the integral to `f z` via D1.
  have h_d1 : ∫ t in (0 : ℝ)..1, chartLocalIntegrandDerivInZ f z₀ z t = f z :=
    integral_chartLocalIntegrandDerivInZ_eq hS_open hS_conv hf hz₀ hz
  rw [← h_d1]
  exact h_derivAt.2

end JacobianChallenge

end
