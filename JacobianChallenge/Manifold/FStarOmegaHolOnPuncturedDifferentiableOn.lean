/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FStarOmegaHolOn
import JacobianChallenge.Manifold.HolomorphicOneFormOnChartCoeff
import JacobianChallenge.Manifold.CriticalValueChartShrink

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `fStarOmegaHolOn`'s `localCoeff` is `DifferentiableOn ℂ` on a punctured
chart ball around a critical value

This file ships the **boundedness-input precursor** for the
`HolomorphicTraceExtension X` item-(2) globalize step: at any critical
value `v₀` of `f`, the chart-`v₀` local coefficient of
`f.fStarOmegaHolOn hnc α` is `DifferentiableOn ℂ` on a *punctured*
chart-target ball around `(chartAt ℂ v₀) v₀`.

Two prior chips compose: `chart_radius_shrink_only_v₀_critical` gives
a chart radius `ρ > 0` whose chart-target ball contains only `v₀`
itself as a critical value of `f`; `HolomorphicOneFormOn.localCoeff_differentiableOn_chartImage`
gives differentiability on the chart image of `regularValueSet ∩
(chartAt ℂ v₀).source`. The punctured ball lies in this chart image
because `(chartAt ℂ v₀).symm` is injective on `(chartAt ℂ v₀).target`
(so excluding `(chartAt ℂ v₀) v₀` forces `(chartAt ℂ v₀).symm w ≠ v₀`,
which combined with the chart-shrink disjunction puts
`(chartAt ℂ v₀).symm w` in `regularValueSet`).

The output is the input format expected by the removable-singularity
adapter (`Manifold/RemovableSingularityAdapter.lean`): once the
n-th-root cancellation bound supplies boundedness, the adapter gives
the analytic extension across the critical value.

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

/-- **Punctured-ball differentiability of `fStarOmegaHolOn`'s `localCoeff`
at a critical value.**

For `f : MeromorphicNonzero X` non-constant, `α : HolomorphicOneForm X`,
and `v₀ ∈ f.criticalValues`, there exists a chart radius `ρ > 0` such
that the chart-target ball of radius `ρ` around `(chartAt ℂ v₀) v₀` is
contained in `(chartAt ℂ v₀).target`, and on the *punctured* ball
`Metric.ball ((chartAt ℂ v₀) v₀) ρ \ {(chartAt ℂ v₀) v₀}`, the
chart-`v₀` local coefficient of `f.fStarOmegaHolOn hnc α` is
`DifferentiableOn ℂ`. -/
theorem fStarOmegaHolOn_localCoeff_differentiableOn_punctured_ball
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v₀ : RiemannSphere} (hv₀ : v₀ ∈ f.criticalValues) :
    ∃ ρ > (0 : ℝ),
      Metric.ball ((chartAt ℂ v₀) v₀) ρ ⊆ (chartAt ℂ v₀).target ∧
      DifferentiableOn ℂ ((f.fStarOmegaHolOn hnc α).localCoeff v₀)
        (Metric.ball ((chartAt ℂ v₀) v₀) ρ \ {(chartAt ℂ v₀) v₀}) := by
  -- Chart shrink: choose ρ > 0 with ball ⊆ chart.target and every w in
  -- ball maps under chart.symm to either a regular value or `v₀` itself.
  obtain ⟨ρ, hρ_pos, hball_sub_target, hball_dichotomy⟩ :=
    chart_radius_shrink_only_v₀_critical f hnc hv₀
  refine ⟨ρ, hρ_pos, hball_sub_target, ?_⟩
  -- DifferentiableOn on the chart image of (regularValueSet ∩ chart.source)
  -- from `HolomorphicOneFormOn.localCoeff_differentiableOn_chartImage`.
  have h_diff_on_chartImage :
      DifferentiableOn ℂ ((f.fStarOmegaHolOn hnc α).localCoeff v₀)
        ((chartAt ℂ v₀) '' (f.regularValueSet ∩ (chartAt ℂ v₀).source)) :=
    HolomorphicOneFormOn.localCoeff_differentiableOn_chartImage
      (f.fStarOmegaHolOn hnc α) v₀
  -- Punctured ball ⊆ chart-image of (regularValueSet ∩ chart.source).
  refine h_diff_on_chartImage.mono ?_
  intro w hw
  -- Unpack: w ∈ ball ρ and w ≠ chart v₀.
  rcases hw with ⟨hw_ball, hw_ne⟩
  have hw_ne' : w ≠ (chartAt ℂ v₀) v₀ := by simpa [Set.mem_singleton_iff] using hw_ne
  -- w ∈ chart.target.
  have hw_target : w ∈ (chartAt ℂ v₀).target := hball_sub_target hw_ball
  -- chart.symm w ∈ chart.source.
  have hsymm_source : (chartAt ℂ v₀).symm w ∈ (chartAt ℂ v₀).source :=
    (chartAt ℂ v₀).map_target hw_target
  -- chart-dichotomy: chart.symm w ∈ regularValueSet ∨ chart.symm w = v₀.
  rcases hball_dichotomy w hw_ball with hsymm_reg | hsymm_eq
  · -- Regular case: chart.symm w ∈ regularValueSet.
    -- We need: w ∈ chart '' (regularValueSet ∩ chart.source).
    refine ⟨(chartAt ℂ v₀).symm w, ⟨hsymm_reg, hsymm_source⟩, ?_⟩
    exact (chartAt ℂ v₀).right_inv hw_target
  · -- Excluded case: chart.symm w = v₀, which forces w = chart v₀
    -- (contradicting hw_ne').
    exfalso
    apply hw_ne'
    have h_chart_eq : (chartAt ℂ v₀) ((chartAt ℂ v₀).symm w) = (chartAt ℂ v₀) v₀ := by
      rw [hsymm_eq]
    have h_right : (chartAt ℂ v₀) ((chartAt ℂ v₀).symm w) = w :=
      (chartAt ℂ v₀).right_inv hw_target
    rw [h_right] at h_chart_eq
    exact h_chart_eq

end MeromorphicNonzero

end JacobianChallenge

end
