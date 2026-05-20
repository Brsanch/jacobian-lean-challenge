/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveSmoothnessFromChartLocal

set_option linter.unusedSectionVars false

/-! # Named chart-local smoothness/FTC hypotheses and composition

This file packages two named hypotheses on `chartLocalPrimitiveExtend` —
`ChartLocalPrimitiveSmoothExt` (smoothness on `φ.source`) and
`ChartLocalPrimitiveFTC` (the FTC identity at every chart-source point) —
and composes them with the bridges from
`PathPrimitiveSmoothnessFromChartLocal.lean` to give the matching
properties of `pathPrimitive` on `φ.source`, **under**
`LoopPeriodVanishes om x₀`.

The named hypotheses are the analytic content currently in progress
in `Manifold/ChartLocalPrimitiveSmoothness.lean` (joint-continuity
helpers already in tree). When discharged, they immediately upgrade
through this composition to chart-local smoothness/FTC of
`pathPrimitive`.

## What this file ships

* `ChartLocalPrimitiveSmoothExt` — smoothness of
  `chartLocalPrimitiveExtend(φ, y) om` on `φ.source`.
* `ChartLocalPrimitiveFTC` — `(om.eval x) = mfderiv
  chartLocalPrimitiveExtend(φ, y) om x` for all `x ∈ φ.source`.
* `pathPrimitive_contMDiffOn_source_of_ChartLocalPrimitiveSmoothExt` —
  the smoothness composition.
* `mfderiv_pathPrimitive_eq_eval_on_source_of_ChartLocalPrimitiveFTC` —
  the FTC composition.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Named hypothesis: `chartLocalPrimitiveExtend(φ, y) om` is
`ContMDiffOn ω` on `φ.source`.** This is the chart-local smoothness
content currently being established in
`Manifold/ChartLocalPrimitiveSmoothness.lean`. -/
def ChartLocalPrimitiveSmoothExt
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : Prop :=
  ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
    (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om)
    φ.source

/-- **Named hypothesis: chart-local FTC at every chart-source point.**
At every `x ∈ φ.source`, `om.eval x = mfderiv ω
(chartLocalPrimitiveExtend(φ, y) om) x`. -/
def ChartLocalPrimitiveFTC
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : Prop :=
  ∀ (x : X) (hx : x ∈ φ.source),
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x

/-- **`pathPrimitive om` is `ContMDiffOn ω` on `φ.source` under
`LoopPeriodVanishes om x₀` + `ChartLocalPrimitiveSmoothExt`.** -/
theorem pathPrimitive_contMDiffOn_source_of_ChartLocalPrimitiveSmoothExt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (h_smooth_ext :
      ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex y hy om) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om)
      φ.source := by
  intro x hx
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  -- Smoothness at x ∈ φ.source from the on-set hypothesis.
  have h_chart_at : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x :=
    (h_smooth_ext x hx).contMDiffAt (h_open.mem_nhds hx)
  -- Transfer to pathPrimitive via the bridge.
  have h_path_at :=
    pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtend_contMDiffAt
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy hx h_chart_at
  exact h_path_at.contMDiffWithinAt

/-- **`mfderiv pathPrimitive = om.eval` on `φ.source` under
`LoopPeriodVanishes om x₀` + `ChartLocalPrimitiveSmoothExt` +
`ChartLocalPrimitiveFTC`.** -/
theorem mfderiv_pathPrimitive_eq_eval_on_source_of_ChartLocalPrimitiveFTC
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (h_smooth_ext :
      ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex y hy om)
    (h_ftc_ext :
      ChartLocalPrimitiveFTC φ h_atlas h_target_convex y hy om)
    (x : X) (hx : x ∈ φ.source) :
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ om) x := by
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  -- Smoothness at x gives differentiability at x.
  have h_chart_at : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x :=
    (h_smooth_ext x hx).contMDiffAt (h_open.mem_nhds hx)
  have h_chart_diff : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x :=
    h_chart_at.mdifferentiableAt (by decide)
  -- FTC at x: om.eval x = mfderiv chartLocalPrimitiveExtend x.
  rw [h_ftc_ext x hx]
  -- mfderiv equality from the bridge.
  exact (mfderiv_pathPrimitive_eq_mfderiv_chartLocalPrimitiveExtend
    h_conn x₀ om h_loop φ h_atlas h_target_convex y hy hx h_chart_diff).symm

end JacobianChallenge

end
