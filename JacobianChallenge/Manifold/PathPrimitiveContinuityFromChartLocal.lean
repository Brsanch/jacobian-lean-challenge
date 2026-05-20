/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtend

set_option linter.unusedSectionVars false

/-! # `ContinuousAt` / `ContinuousOn` transfer for `pathPrimitive`

Mirror of `PathPrimitiveSmoothnessFromChartLocal.lean` at the
*continuity* level: under `LoopPeriodVanishes om x₀`, the
`ContinuousAt` (and `ContinuousOn φ.source`) regularity of
`chartLocalPrimitiveExtend` transfers to `pathPrimitive` via
`Filter.EventuallyEq` (or set-level `EqOn`).

The continuity of `chartLocalPrimitiveExtend` on `φ.source` is the
*continuity sub-chip* of the chart-local primitive's E-arc, in progress
in `Manifold/ChartLocalPrimitiveSmoothness.lean` via mathlib's
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.
This file ships the transfer; users who supply the continuity input get
`Continuous` of `pathPrimitive om` on `φ.source`.

## What this file ships

* `pathPrimitive_continuousAt_of_chartLocalPrimitiveExtend_continuousAt`
  — pointwise transfer.
* `pathPrimitive_continuousOn_of_chartLocalPrimitiveExtend_continuousOn`
  — set-level transfer over `φ.source`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Transfer `ContinuousAt` from `chartLocalPrimitiveExtend` to
`pathPrimitive` at a point.**

If `chartLocalPrimitiveExtend(φ, y) om` is `ContinuousAt` at
`x ∈ φ.source`, then `pathPrimitive h_conn x₀ om` is also
`ContinuousAt` at `x`. Proof: the two differ by an additive constant
on a neighborhood of `x` (the bridge from
`ChartLocalPrimitiveExtend.lean`), so `ContinuousAt` propagates via
`ContinuousAt.add` + `continuousAt_const` plus
`ContinuousAt.congr` along the `EventuallyEq`. -/
theorem pathPrimitive_continuousAt_of_chartLocalPrimitiveExtend_continuousAt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source)
    (h_chart_cts : ContinuousAt
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x) :
    ContinuousAt (pathPrimitive h_conn x₀ om) x := by
  have h_const :
      ContinuousAt (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    continuousAt_const
  have h_sum :
      ContinuousAt (fun x' : X =>
        chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y) x :=
    h_chart_cts.add h_const
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy x hx
  exact h_sum.congr h_eq.symm

/-- **Transfer `ContinuousOn φ.source` from `chartLocalPrimitiveExtend` to
`pathPrimitive` over a chart.**

If `chartLocalPrimitiveExtend(φ, y) om` is `ContinuousOn φ.source`,
then `pathPrimitive h_conn x₀ om` is also `ContinuousOn φ.source`.
Proof: at any point of `φ.source`, use the pointwise transfer plus
`ContinuousAt.continuousOn`. -/
theorem pathPrimitive_continuousOn_of_chartLocalPrimitiveExtend_continuousOn
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (h_chart_cts : ContinuousOn
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om)
      φ.source) :
    ContinuousOn (pathPrimitive h_conn x₀ om) φ.source := by
  intro x hx
  -- At a point of φ.source, ContinuousAt suffices because φ.source is open.
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  have h_chart_cts_at : ContinuousAt
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x :=
    (h_chart_cts x hx).continuousAt (h_open.mem_nhds hx)
  have h_path_cts_at :=
    pathPrimitive_continuousAt_of_chartLocalPrimitiveExtend_continuousAt
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy hx h_chart_cts_at
  exact h_path_cts_at.continuousWithinAt

end JacobianChallenge

end
