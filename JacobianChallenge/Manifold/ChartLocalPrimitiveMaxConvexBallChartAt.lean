/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ConvexBallChartAtMaximalAtlas
import JacobianChallenge.Manifold.ChartLocalPrimitiveMax
import JacobianChallenge.Manifold.ChartLocalPrimitive

set_option linter.unusedSectionVars false

/-! # `chartLocalPrimitiveMax` at `convexBallChartAt y` ≡ `chartLocalPrimitive` at `chartAt y`

`convexBallChartAt y` shares its chart map (`= chartAt ℂ y`) and inverse
(`= (chartAt ℂ y).symm`) with the canonical `chartAt ℂ y` (both
identities are `rfl` — see `convexBallChartAt_coe`,
`convexBallChartAt_coe_symm`). Consequently, the `SmoothPath`
constructed by `linearInChartSegmentMax` from the two charts at the
same endpoints is the same underlying path: the `toPath` field is
`fun t => φ.symm (bumpedSegment (φ y) (φ x) t)` in both cases and is
`rfl`-equal, while the remaining fields are Props that match by
proof irrelevance.

This file establishes the path-level bridge that lets the analytic
content from the atlas-form chartAt headlines be reused on the
maximal-atlas convexBallChartAt y discharge target. The bridge is
parameterised by a hypothesis `h_target_convex_chartAt` for chartAt y;
when convexBallChartAt y is in play, the consumer will provide the
canonical such hypothesis when available (or instantiate against an
arbitrary convex sub-target containing the segment).

## What this file ships

* `linearInChartSegmentMax_convexBallChartAt_eq_chartAtMax` — the
  underlying `SmoothPath` produced via `linearInChartSegmentMax` for
  `convexBallChartAt y` equals the one produced via `chartAt ℂ y`
  (Max-form, atlas-membership via `subset_maximalAtlas`).
* `chartLocalPrimitiveMax_convexBallChartAt_eq_chartLocalPrimitiveMax_chartAt`
  — corresponding equality of the chart-local primitive values.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Path-level bridge: `linearInChartSegmentMax (convexBallChartAt y) … x …`
equals `linearInChartSegmentMax (chartAt ℂ y) … x …` as `SmoothPath`s.**

Both `SmoothPath` values have:
* identical `src = y`, `tgt = x` (rfl);
* identical `toPath.toFun = fun s => φ.symm (bumpedSegment (φ y) (φ x) s.val)`,
  since `(convexBallChartAt y : X → ℂ) = (chartAt ℂ y : X → ℂ)` and
  `((convexBallChartAt y).symm : ℂ → X) = ((chartAt ℂ y).symm : ℂ → X)`
  are both `rfl`;
* `toPath.{continuous_toFun,source',target'}` and `smooth` are Props,
  equal by proof irrelevance.

Hence the `SmoothPath` values are equal by `SmoothPath` `rfl`. -/
lemma SmoothPath.linearInChartSegmentMax_convexBallChartAt_eq_chartAtMax
    (y x : X)
    (hy_ball : y ∈ (convexBallChartAt y).source)
    (hx_ball : x ∈ (convexBallChartAt y).source)
    (hy_chartAt : y ∈ (chartAt ℂ y).source)
    (hx_chartAt : x ∈ (chartAt ℂ y).source)
    (h_seg_ball : segment ℝ ((convexBallChartAt y) y) ((convexBallChartAt y) x)
      ⊆ (convexBallChartAt y).target)
    (h_seg_chartAt : segment ℝ ((chartAt ℂ y) y) ((chartAt ℂ y) x)
      ⊆ (chartAt ℂ y).target) :
    SmoothPath.linearInChartSegmentMax (convexBallChartAt y)
        (convexBallChartAt_mem_maximalAtlas_real y)
        y x hy_ball hx_ball h_seg_ball
      = SmoothPath.linearInChartSegmentMax (chartAt ℂ y)
          (IsManifold.subset_maximalAtlas (n := ⊤)
            (chart_mem_atlas ℂ y))
          y x hy_chartAt hx_chartAt h_seg_chartAt := by
  rfl

/-- **Value-level bridge: `chartLocalPrimitiveMax (convexBallChartAt y) …`
equals `chartLocalPrimitiveMax (chartAt ℂ y) …` (Max-form via
`subset_maximalAtlas`).** Direct consequence of the path-level bridge:
`chartLocalPrimitiveMax` is `complexChainPeriod ∘ SmoothChain.single`
of the segment path, and the two paths are equal by the previous lemma. -/
lemma chartLocalPrimitiveMax_convexBallChartAt_eq_chartAtMax
    (y x : X)
    (hy_ball : y ∈ (convexBallChartAt y).source)
    (hx_ball : x ∈ (convexBallChartAt y).source)
    (hy_chartAt : y ∈ (chartAt ℂ y).source)
    (hx_chartAt : x ∈ (chartAt ℂ y).source)
    (h_target_convex_ball : Convex ℝ (convexBallChartAt y).target)
    (h_target_convex_chartAt : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    chartLocalPrimitiveMax (convexBallChartAt y)
        (convexBallChartAt_mem_maximalAtlas_real y)
        h_target_convex_ball y hy_ball om x hx_ball
      = chartLocalPrimitiveMax (chartAt ℂ y)
          (IsManifold.subset_maximalAtlas (n := ⊤)
            (chart_mem_atlas ℂ y))
          h_target_convex_chartAt y hy_chartAt om x hx_chartAt := rfl

/-- **Path-level bridge across chart forms: `linearInChartSegmentMax (convexBallChartAt y) …`
equals `linearInChartSegment (chartAt ℂ y) (atlas form) …` as `SmoothPath`s.**

Same rfl argument as the previous lemma extended one more rfl step
(`linearInChartSegmentMax (chartAt y) (subset_maximalAtlas …) =
linearInChartSegment (chartAt y) (chart_mem_atlas) …` via the existing
`SmoothPath.linearInChartSegmentMax_eq_linearInChartSegment` bridge). -/
lemma SmoothPath.linearInChartSegmentMax_convexBallChartAt_eq_chartAt_atlas
    (y x : X)
    (hy_ball : y ∈ (convexBallChartAt y).source)
    (hx_ball : x ∈ (convexBallChartAt y).source)
    (hy_chartAt : y ∈ (chartAt ℂ y).source)
    (hx_chartAt : x ∈ (chartAt ℂ y).source)
    (h_seg_ball : segment ℝ ((convexBallChartAt y) y) ((convexBallChartAt y) x)
      ⊆ (convexBallChartAt y).target)
    (h_seg_chartAt : segment ℝ ((chartAt ℂ y) y) ((chartAt ℂ y) x)
      ⊆ (chartAt ℂ y).target) :
    SmoothPath.linearInChartSegmentMax (convexBallChartAt y)
        (convexBallChartAt_mem_maximalAtlas_real y)
        y x hy_ball hx_ball h_seg_ball
      = SmoothPath.linearInChartSegment (chartAt ℂ y) (chart_mem_atlas ℂ y)
          y x hy_chartAt hx_chartAt h_seg_chartAt := by
  rfl

/-- **Value bridge to atlas-form `chartLocalPrimitive`.** When the
hypotheses are matched (and any choice of `Convex ℝ (chartAt ℂ y).target`
is provided), `chartLocalPrimitiveMax (convexBallChartAt y) …` equals
`chartLocalPrimitive (chartAt ℂ y) …`. Direct corollary of the path-level
rfl bridge: `chartLocalPrimitive` is defined as `complexChainPeriod ∘
SmoothChain.single ∘ linearInChartSegment`, and the underlying
`linearInChartSegment(Max)` calls reduce to the same `SmoothPath`. -/
lemma chartLocalPrimitiveMax_convexBallChartAt_eq_chartLocalPrimitive_chartAt
    (y x : X)
    (hy_ball : y ∈ (convexBallChartAt y).source)
    (hx_ball : x ∈ (convexBallChartAt y).source)
    (hy_chartAt : y ∈ (chartAt ℂ y).source)
    (hx_chartAt : x ∈ (chartAt ℂ y).source)
    (h_target_convex_chartAt : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    chartLocalPrimitiveMax (convexBallChartAt y)
        (convexBallChartAt_mem_maximalAtlas_real y)
        (convexBallChartAt_target_convex y) y hy_ball om x hx_ball
      = chartLocalPrimitive (chartAt ℂ y) (chart_mem_atlas ℂ y)
          h_target_convex_chartAt y hy_chartAt om x hx_chartAt := rfl

end JacobianChallenge

end
