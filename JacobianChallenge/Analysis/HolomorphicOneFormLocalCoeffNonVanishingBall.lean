/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormLocalCoeffAtBase
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Non-vanishing ball for `localCoeff` of a nonzero holomorphic 1-form

Combines chip E.1 (existence of a chart `y` and point `z₀ = (chartAt
ℂ y) y` with `localCoeff om y z₀ ≠ 0`) with the in-tree analyticity
of `localCoeff om y` on the chart target
(`Manifold/HolomorphicOneFormChartCoeffOnTarget`) and standard
continuity to produce an **open ball around `z₀` inside the chart
target on which `localCoeff om y` is everywhere nonzero**.

This is chip E.2 of the positivity arc. Chip E.3 will then integrate
this non-vanishing-ball statement into `∫⁻ … > 0`, and chip E.4 will
combine with the partition-of-unity sum to get `0 <
globalPettersonL2Sq om f` for `om ≠ 0`.

Headline:

```
theorem exists_nonvanishing_ball_of_ne_zero (om : HolomorphicOneForm X) (h : om ≠ 0) :
    ∃ y : X, ∃ z₀ : ℂ, ∃ ε > 0,
      Metric.ball z₀ ε ⊆ (chartAt ℂ y).target ∧
      ∀ z ∈ Metric.ball z₀ ε, localCoeff om y z ≠ 0
```

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff Topology

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Non-vanishing ball for `localCoeff` of a nonzero holomorphic 1-form.**

Combining chip E.1 (existence-at-base-chart-image) with continuity of
`localCoeff om y` on the chart target, we get an open ball around the
chart image of `y` inside the chart target on which `localCoeff om y`
never vanishes. -/
theorem exists_nonvanishing_ball_of_ne_zero
    (om : HolomorphicOneForm X) (h : om ≠ 0) :
    ∃ y : X, ∃ z₀ : ℂ, ∃ ε > (0 : ℝ),
      Metric.ball z₀ ε ⊆ (chartAt ℂ y).target ∧
      ∀ z ∈ Metric.ball z₀ ε, localCoeff om y z ≠ 0 := by
  -- Pick y where localCoeff is nonzero at the chart image of y itself.
  obtain ⟨y, hy⟩ := exists_localCoeff_at_chartAt_self_ne_zero_of_ne_zero om h
  set z₀ : ℂ := (chartAt ℂ y) y with hz₀
  refine ⟨y, z₀, ?_⟩
  -- Continuity of localCoeff om y on the chart target.
  have h_cont_on : ContinuousOn (localCoeff om y) (chartAt ℂ y).target :=
    (localCoeff_analyticOn om y).continuousOn
  -- z₀ ∈ chart target (since y ∈ chart source).
  have hz₀_mem : z₀ ∈ (chartAt ℂ y).target := by
    rw [hz₀]; exact mem_chart_target ℂ y
  -- Open chart target → continuousAt at z₀.
  have h_cont_at : ContinuousAt (localCoeff om y) z₀ :=
    (h_cont_on z₀ hz₀_mem).continuousAt
      ((chartAt ℂ y).open_target.mem_nhds hz₀_mem)
  -- Use ContinuousAt.eventually_ne to get a nhd where localCoeff ≠ 0.
  have h_ne_eventually : ∀ᶠ z in 𝓝 z₀, localCoeff om y z ≠ 0 :=
    h_cont_at.eventually_ne hy
  -- Intersect with open chart target neighborhood at z₀.
  have h_target_eventually : ∀ᶠ z in 𝓝 z₀, z ∈ (chartAt ℂ y).target :=
    (chartAt ℂ y).open_target.mem_nhds hz₀_mem
  have h_both : ∀ᶠ z in 𝓝 z₀,
      z ∈ (chartAt ℂ y).target ∧ localCoeff om y z ≠ 0 :=
    h_target_eventually.and h_ne_eventually
  -- Convert eventually-in-nhds to ball form.
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.eventually_nhds_iff_ball.mp h_both
  refine ⟨ε, hε_pos, ?_, ?_⟩
  · intro z hz
    exact (hε_ball z hz).1
  · intro z hz
    exact (hε_ball z hz).2

end HolomorphicOneForm

end
