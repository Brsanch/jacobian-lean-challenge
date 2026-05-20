/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveContinuityFromChartLocal
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamed

set_option linter.unusedSectionVars false

/-! # Named `ChartLocalPrimitiveContinuousExt` + composition

Continuity-level mirror of `PathPrimitiveLocalSmoothFTCNamed.lean`:
packages the chart-local continuity of `chartLocalPrimitiveExtend` as a
named hypothesis and composes with the bridge from
`PathPrimitiveContinuityFromChartLocal.lean` to give `ContinuousOn` of
`pathPrimitive om` on `φ.source` under `LoopPeriodVanishes om x₀`.

This is the structurally clean parallel of the smoothness arc, separable
from full smoothness for use cases where only continuity is needed
(e.g., as an early sub-chip of the in-progress chart-local primitive
analytic arc in `Manifold/ChartLocalPrimitiveSmoothness.lean`).

## What this file ships

* `ChartLocalPrimitiveContinuousExt` — named hypothesis.
* `pathPrimitive_continuousOn_source_of_ChartLocalPrimitiveContinuousExt`
  — composition.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Named hypothesis: `chartLocalPrimitiveExtend(φ, y) om` is
`ContinuousOn` `φ.source`.** Mirror of `ChartLocalPrimitiveSmoothExt`
at the continuity level. -/
def ChartLocalPrimitiveContinuousExt
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : Prop :=
  ContinuousOn (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om)
    φ.source

/-- **`pathPrimitive om` is `ContinuousOn` `φ.source` under
`LoopPeriodVanishes om x₀` + `ChartLocalPrimitiveContinuousExt`.** -/
theorem pathPrimitive_continuousOn_source_of_ChartLocalPrimitiveContinuousExt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (h_cts_ext :
      ChartLocalPrimitiveContinuousExt φ h_atlas h_target_convex y hy om) :
    ContinuousOn (pathPrimitive h_conn x₀ om) φ.source :=
  pathPrimitive_continuousOn_of_chartLocalPrimitiveExtend_continuousOn
    h_conn x₀ om h_loop φ h_atlas h_target_convex y hy h_cts_ext

/-- **`ChartLocalPrimitiveSmoothExt` implies `ChartLocalPrimitiveContinuousExt`.**
Smoothness is strictly stronger than continuity. -/
theorem chartLocalPrimitiveContinuousExt_of_smoothExt
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X)
    (h_smooth :
      ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex y hy om) :
    ChartLocalPrimitiveContinuousExt φ h_atlas h_target_convex y hy om :=
  h_smooth.continuousOn

end JacobianChallenge

end
