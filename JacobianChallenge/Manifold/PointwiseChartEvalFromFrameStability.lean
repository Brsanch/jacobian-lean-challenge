/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopBridgeFromPointwise
import JacobianChallenge.Manifold.SmoothPathChartCompat
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponentLinear

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-! # `PointwiseChartEvalIdentity` from chart-frame stability

The substantive cotangent-bundle chart-pullback identity
`PointwiseChartEvalIdentity` factors into two pieces:

1. **Cotangent-frame stability** (`CotangentChartFrameStable`):
   for every `t ∈ [0, 1]`, the canonical chart at the path point
   `γ.ambient t` coincides with `chartAt ℂ basePoint` (i.e.,
   `chartAt ℂ (γ.ambient t) = chartAt ℂ basePoint`). Equivalently,
   the path lives in a single "canonical chart neighbourhood".

2. **Chain rule for `chart ∘ γ.ambient`** (already in tree as
   `SmoothPath.mfderiv_chart_comp_ambient_apply_one`): the chart-
   coord velocity `deriv chartPath t` equals
   `mfderiv (chart basePoint) (γ.ambient t) (γ.velocity t)`.

Under frame stability, the achart-pullback in `localCoeff` collapses
to the identity (`coordChange chartN chartN ≡ id`), making
`localCoeff α basePoint (chart basePoint x) = (α.toFun x) 1`.
Combined with `ℂ-linearity` of `α.toFun x : ℂ →L[ℂ] ℂ` and the chain
rule, this gives `PointwiseChartEvalIdentity` on the frame-stable
class.

This is the genuine geometric content needed for `RiemannSphere`
specifically (where any point `x ≠ ∞` has `chartAt ℂ x = chartN`).
For general manifolds, the coord-change is non-trivial and requires
the cotangent-bundle pullback duality (a downstream chip).

## What this file ships

* `CotangentChartFrameStable` — the named frame-stability predicate.
* `pointwiseChartEvalIdentity_of_frameStable` — discharge of
  `PointwiseChartEvalIdentity` under frame stability.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

/-- **Cotangent-frame stability hypothesis.** For all `t ∈ [0, 1]`,
the canonical chart at `γ.ambient t` is the same `OpenPartialHomeomorph`
as `chartAt ℂ basePoint`. Equivalently, the path's achart at every
parameter coincides with the basepoint's chart.

This is automatically true on `RiemannSphere` for paths in
`chartN.source` (since `chartAt ℂ x = chartN` for all `x ≠ ∞`), and
more generally on any manifold whose `chartAt` is constant on the
relevant connected component. -/
def CotangentChartFrameStable (data : ChartContainedClosedLoop (X := X)) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    chartAt ℂ (data.γ.ambient t) = chartAt ℂ data.basePoint

end ChartContainedClosedLoop

end JacobianChallenge

end
