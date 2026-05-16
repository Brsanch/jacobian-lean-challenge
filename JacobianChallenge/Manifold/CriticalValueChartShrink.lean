/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import Mathlib.Topology.MetricSpace.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Chart-radius shrink at a critical value: only `v₀` critical in chart

For `f : MeromorphicNonzero X` non-constant and a critical value
`v₀ ∈ f.criticalValues`, there exists a chart radius `ρ > 0` such that
every point of the chart-target ball `ball ((chartAt ℂ v₀) v₀) ρ` is
either the chart image `(chartAt ℂ v₀) v₀` itself, or the chart image
of a *regular* value of `f`.

I.e. on this restricted chart neighbourhood of `v₀`, the only critical
value of `f` is `v₀`.

This is the topological set-up step for the
`HolomorphicTraceExtension X` item-(2) globalize: we apply removable
singularity at the *single* puncture `(chartAt ℂ v₀) v₀` to extend the
chart-coord representative of `f.fStarOmegaHolOn hnc α` from the
punctured chart disc to the full chart disc.

## Construction

`f.criticalValues \ {v₀}` is finite (subset of finite), hence closed in
T1 `RiemannSphere`. Its complement is open and contains `v₀`. Intersect
with the open chart source `(chartAt ℂ v₀).source` to get an open
`U ∋ v₀`. The chart is an open partial homeomorphism, so
`(chartAt ℂ v₀) '' U` is open in `RiemannSphere`'s codomain `ℂ`.
Choose `ρ > 0` with `ball ((chartAt ℂ v₀) v₀) ρ ⊆ (chartAt ℂ v₀) '' U`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology ContDiff
open Set

noncomputable section

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chart-radius shrink at a critical value.**

For `f` non-constant and `v₀ ∈ f.criticalValues`, there exists `ρ > 0`
with the chart-target ball of radius `ρ` around `(chartAt ℂ v₀) v₀`
contained in `(chartAt ℂ v₀).target`, and every point of that ball
either chart-maps back to `v₀` itself or to a regular value of `f`. -/
theorem chart_radius_shrink_only_v₀_critical
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v₀ : RiemannSphere} (_hv₀ : v₀ ∈ f.criticalValues) :
    ∃ ρ > (0 : ℝ),
      Metric.ball ((chartAt ℂ v₀) v₀) ρ ⊆ (chartAt ℂ v₀).target ∧
      ∀ w ∈ Metric.ball ((chartAt ℂ v₀) v₀) ρ,
        (chartAt ℂ v₀).symm w ∈ f.regularValueSet ∨
        (chartAt ℂ v₀).symm w = v₀ := by
  -- 1. `criticalValues \ {v₀}` is finite, hence closed in T1 `RiemannSphere`.
  have h_cv_fin : f.criticalValues.Finite := f.criticalValues_finite hnc
  have h_cv_minus_fin : (f.criticalValues \ {v₀}).Finite :=
    h_cv_fin.subset diff_subset
  have h_cv_minus_closed : IsClosed (f.criticalValues \ {v₀}) :=
    h_cv_minus_fin.isClosed
  have h_compl_open : IsOpen ((f.criticalValues \ {v₀})ᶜ) :=
    h_cv_minus_closed.isOpen_compl
  -- 2. `v₀ ∈ (criticalValues \ {v₀})ᶜ`.
  have h_v₀_compl : v₀ ∈ (f.criticalValues \ {v₀})ᶜ := by
    intro h_in; exact h_in.2 rfl
  have h_v₀_source : v₀ ∈ (chartAt ℂ v₀).source := mem_chart_source ℂ v₀
  -- 3. `U` is open, contains `v₀`, ⊆ chart source.
  set U : Set RiemannSphere :=
    (f.criticalValues \ {v₀})ᶜ ∩ (chartAt ℂ v₀).source with hU_def
  have hU_open : IsOpen U :=
    h_compl_open.inter (chartAt ℂ v₀).open_source
  have hU_v₀ : v₀ ∈ U := ⟨h_v₀_compl, h_v₀_source⟩
  have hU_sub_source : U ⊆ (chartAt ℂ v₀).source := inter_subset_right
  -- 4. Chart-image of U is open in ℂ.
  have h_chart_im_open : IsOpen ((chartAt ℂ v₀) '' U) :=
    (chartAt ℂ v₀).isOpen_image_of_subset_source hU_open hU_sub_source
  -- 5. `chartAt v₀ v₀ ∈ chart '' U`.
  have h_chart_v₀_in_im : (chartAt ℂ v₀) v₀ ∈ (chartAt ℂ v₀) '' U :=
    ⟨v₀, hU_v₀, rfl⟩
  -- 6. `chart '' U ⊆ chart.target`.
  have h_chart_im_sub_target : (chartAt ℂ v₀) '' U ⊆ (chartAt ℂ v₀).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (chartAt ℂ v₀).map_source (hU_sub_source hy)
  -- 7. Pick ρ > 0 with `ball (chart v₀) ρ ⊆ chart '' U`.
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ :=
    Metric.isOpen_iff.mp h_chart_im_open _ h_chart_v₀_in_im
  refine ⟨ρ, hρ_pos, ?_, ?_⟩
  · -- ball ⊆ chart.target via chart '' U ⊆ chart.target.
    exact hρ_sub.trans h_chart_im_sub_target
  · -- chart.symm w ∈ regularValueSet ∨ chart.symm w = v₀ for w in ball.
    intro w hw
    obtain ⟨y, hy_U, hy_w⟩ := hρ_sub hw
    -- chart.symm w = y by chart's left-inverse, since y ∈ chart.source.
    have h_symm_w_eq_y : (chartAt ℂ v₀).symm w = y := by
      rw [← hy_w]
      exact (chartAt ℂ v₀).left_inv (hU_sub_source hy_U)
    rw [h_symm_w_eq_y]
    -- y ∈ U means y ∈ (criticalValues \ {v₀})ᶜ.
    have hy_not_minus : y ∉ f.criticalValues \ {v₀} := hy_U.1
    -- Either y ∉ criticalValues (regular) or y = v₀.
    by_cases h_y_v₀ : y = v₀
    · right; exact h_y_v₀
    · left
      -- `y ∉ f.criticalValues \ {v₀}` and `y ≠ v₀` ⇒ `y ∉ f.criticalValues`.
      have : y ∉ f.criticalValues := by
        intro h_in_cv
        exact hy_not_minus ⟨h_in_cv, h_y_v₀⟩
      -- regularValueSet = criticalValues ᶜ, so y ∉ critical ⇒ y ∈ regular.
      exact this

end MeromorphicNonzero

end JacobianChallenge

end
