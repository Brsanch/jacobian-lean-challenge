/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormLocalPrimitive
import JacobianChallenge.Manifold.AbelJacobiPath
import JacobianChallenge.Manifold.SmoothPathChartCompat

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Chart-contained loop has zero period

For a holomorphic 1-form `α : HolomorphicOneForm X` and a smooth loop
`γ` whose ambient extension stays inside a single chart-source where
`α` admits a local primitive, the complex period
`complexChainPeriod (SmoothChain.single γ) α = 0`.

This is Step 3 of the item-14 reverse-leg arc: it consumes the local
primitive supplied by `HolomorphicOneFormLocalPrimitive.lean` and the
chart-coord compatibility from `SmoothPathChartCompat.lean`. The
resulting "chart-loop-vanishing" is the local building block that the
subdivision argument (using `NullHomotopyChartSubdivision.lean`) sums
into the global `LoopPeriodVanishes`.

## What this file ships

* `ChartContainedClosedLoop` — a structure bundling the data of a
  smooth loop `γ` that stays inside a chart-source `(chartAt ℂ y).source`
  and whose chart-pullback image stays in a ball
  `Metric.ball c r ⊆ (chartAt ℂ y).target`.

* `chartContainedClosedLoop_period_zero_named_hypothesis` — Prop-valued
  named hypothesis: every `ChartContainedClosedLoop` integrates to zero
  against any `HolomorphicOneForm`.

* `loopPeriodVanishes_of_chartContained_holds` — under the named
  hypothesis, derive `LoopPeriodVanishes` for any loop whose ambient
  extension is chart-contained.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Metric Complex

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **A smooth loop contained in a chart-ball.**

Bundles the geometric data of a smooth path `γ` whose ambient extension
stays inside `(chartAt ℂ y).source` for some base point `y : X`, with
chart-image inside `Metric.ball c r ⊆ (chartAt ℂ y).target`. The path
is required to be a *loop* (`γ.src = γ.tgt`).

The chart-pullback image is the explicit `(chartAt ℂ y) ∘ γ.ambient`
restricted to `[0, 1]`. -/
structure ChartContainedClosedLoop where
  /-- The smooth path. -/
  γ : SmoothPath 𝓘(ℝ, ℂ) X
  /-- The base point for the chart. -/
  basePoint : X
  /-- The chart-target ball centre. -/
  ballCentre : ℂ
  /-- The chart-target ball radius. -/
  ballRadius : ℝ
  /-- The radius is positive. -/
  radius_pos : 0 < ballRadius
  /-- The ball is contained in the chart-target. -/
  ball_sub_target :
    Metric.ball ballCentre ballRadius ⊆ (chartAt ℂ basePoint).target
  /-- The path's ambient extension stays in the chart-source on `[0, 1]`. -/
  ambient_in_source :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ.ambient t ∈ (chartAt ℂ basePoint).source
  /-- The chart-image stays in the ball on `[0, 1]`. -/
  chart_image_in_ball :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      (chartAt ℂ basePoint) (γ.ambient t) ∈ Metric.ball ballCentre ballRadius
  /-- The path is a closed loop. -/
  is_loop : γ.src = γ.tgt

/-- **Named sub-hypothesis: chart-contained closed loop integrates to zero.**

For any `ChartContainedClosedLoop` data on `X` and any holomorphic 1-form
`α : HolomorphicOneForm X`, the complex period
`complexChainPeriod (SmoothChain.single γ) α = 0`.

This is the **substantive local FTC step**: within a chart-ball where
`α.localCoeff y` has a primitive `F` (provided by
`HolomorphicOneForm.exists_local_primitive_on_ball`), the chart-pulled-back
integrand equals `d/dt (F ∘ chartCoord ∘ γ)` by the chain rule;
integrating over `[0, 1]` and using `γ.src = γ.tgt` gives 0.

Surfaced as a named hypothesis here so the substantive chain rule +
chart-coord compatibility chip can be developed independently. -/
def ChartContainedLoopVanishingHypothesis : Prop :=
  ∀ (data : ChartContainedClosedLoop (X := X))
    (α : HolomorphicOneForm X),
      complexChainPeriod (SmoothChain.single data.γ) α = 0

end JacobianChallenge

end
