/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothExtChartAt
import JacobianChallenge.Manifold.ChartLocalPrimitiveFTCChartAt
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamedMax

set_option linter.unusedSectionVars false

/-! # Maximal-atlas lifts of the chartAt SmoothExt / FTC dischargers

The atlas-form headlines

  `chartLocalPrimitiveSmoothExt_chartAt`
    : `ChartLocalPrimitiveSmoothExt (chartAt ℂ y) (chart_mem_atlas ℂ y) …`
  `chartLocalPrimitiveFTC_chartAt`
    : `ChartLocalPrimitiveFTC (chartAt ℂ y) (chart_mem_atlas ℂ y) …`

discharge the chart-local smoothness / FTC named hypotheses at the
canonical chart `chartAt ℂ y`. This file lifts them to the maximal-atlas
forms

  `chartLocalPrimitiveSmoothExtMax_chartAt`
    : `ChartLocalPrimitiveSmoothExtMax (chartAt ℂ y)
        (subset_maximalAtlas (chart_mem_atlas ℂ y)) …`
  `chartLocalPrimitiveFTCMax_chartAt`
    : `ChartLocalPrimitiveFTCMax (chartAt ℂ y)
        (subset_maximalAtlas (chart_mem_atlas ℂ y)) …`

via the bridge `chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveExtend`
(equality of the two total-function wrappers as functions `X → ℂ` when
`h_atlas` is available). For `chartAt ℂ y` with convex target, these are
unconditional Max-form discharges.

Note. These lift the Max-form discharge to the *canonical* chart only.
The intended downstream consumer of the Max forms is
`convexBallChartAt y = (chartAt ℂ y).restr (chartBallSourcePreimage y)`,
which has convex target unconditionally on arbitrary X but is **not**
literally `chartAt ℂ y`. Bridging to `convexBallChartAt y` is a
separate cascade step that uses the fact that `(restr φ).symm = φ.symm`
on the restricted source — defer to the next chip.

## Manifold-structure precondition

The atlas-form discharges live under `[IsManifold (𝓘(ℂ, ℂ)) ω X]`. The
Max-named hypotheses are typed at `IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X`.
Both downgrades are automatic instances:
* `[IsManifold (𝓘(ℂ, ℂ)) ω X] → [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]` (mathlib's
  `IsManifold.of_le le_top` instance on ω);
* `[IsManifold (𝓘(ℂ, ℂ)) ω X] → [IsManifold (𝓘(ℝ, ℂ)) ⊤ X]`
  (`complexManifoldRealification` in tree).

So this file's variable section requires only `[IsManifold (𝓘(ℂ, ℂ)) ω X]`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`ChartLocalPrimitiveSmoothExtMax` at the canonical chart `chartAt ℂ y`
UNCONDITIONALLY** (modulo the convex chart-target hypothesis). Direct
lift of the atlas-form `chartLocalPrimitiveSmoothExt_chartAt` via the
bridge between the two total-function wrappers. -/
theorem chartLocalPrimitiveSmoothExtMax_chartAt
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    ChartLocalPrimitiveSmoothExtMax (chartAt ℂ y)
      (IsManifold.subset_maximalAtlas (n := ⊤) (chart_mem_atlas ℂ y))
      h_target_convex y (mem_chart_source ℂ y) om := by
  unfold ChartLocalPrimitiveSmoothExtMax
  rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveExtend
      (chartAt ℂ y) (chart_mem_atlas ℂ y) h_target_convex y
      (mem_chart_source ℂ y) om]
  exact chartLocalPrimitiveSmoothExt_chartAt y h_target_convex om

/-- **`ChartLocalPrimitiveFTCMax` at the canonical chart `chartAt ℂ y`
UNCONDITIONALLY** (modulo the convex chart-target hypothesis). Direct
lift of the atlas-form `chartLocalPrimitiveFTC_chartAt` via the bridge
between the two total-function wrappers. -/
theorem chartLocalPrimitiveFTCMax_chartAt
    (y : X) (h_target_convex : Convex ℝ (chartAt ℂ y).target)
    (om : HolomorphicOneForm X) :
    ChartLocalPrimitiveFTCMax (chartAt ℂ y)
      (IsManifold.subset_maximalAtlas (n := ⊤) (chart_mem_atlas ℂ y))
      h_target_convex y (mem_chart_source ℂ y) om := by
  intro x hx
  have h := chartLocalPrimitiveFTC_chartAt y h_target_convex om x hx
  -- h : om.eval x = mfderiv … (chartLocalPrimitiveExtend …) x.
  -- Goal: om.eval x = mfderiv … (chartLocalPrimitiveExtendMax …) x.
  -- The two functions are pointwise-equal as `X → ℂ`, so their mfderivs
  -- agree at x.
  rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveExtend
      (chartAt ℂ y) (chart_mem_atlas ℂ y) h_target_convex y
      (mem_chart_source ℂ y) om]
  exact h

end JacobianChallenge

end
