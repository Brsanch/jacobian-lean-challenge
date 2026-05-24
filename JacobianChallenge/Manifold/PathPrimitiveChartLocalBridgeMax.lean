/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveMax
import JacobianChallenge.Manifold.PathPrimitiveChartLocalBridge

set_option linter.unusedSectionVars false

/-! # Maximal-atlas variant of the `pathPrimitive` ↔ `chartLocalPrimitive` bridge

Parallel to `PathPrimitiveChartLocalBridge.lean` but parameterised by
`h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X` instead of
`h_atlas : φ ∈ atlas ℂ X`. Same construction: pick any smooth path
`α : x₀ ⇝ y` from `h_conn`, concatenate with the chart-line segment
`β : y ⇝ x` (now built via `SmoothPath.linearInChartSegmentMax`), apply
`pathPrimitive_eq_integral_of_loopPeriodVanishes` together with
`complexChainPeriod_single_concat`, then collapse the chart-line side
to `chartLocalPrimitiveMax` by definitional unfolding.

## What this file ships

* `pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocalMax` —
  the maximal-atlas form of the local decomposition.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Maximal-atlas form of the local decomposition of `pathPrimitive`
via a chart-line segment.**

For a global basepoint `x₀ : X` and a holomorphic 1-form `om` with
vanishing loop periods at `x₀`, the global path-primitive at any
point `x` in a chart `φ` of the ℝ-`⊤` maximal atlas with convex
target decomposes as the path-primitive at the chart-basepoint `y`
plus the chart-local primitive from `y` to `x`:

  `pathPrimitive h_conn x₀ om x =
   pathPrimitive h_conn x₀ om y + chartLocalPrimitiveMax(φ, y) om x`.

Same proof as the atlas form, with the chart-line segment built via
`SmoothPath.linearInChartSegmentMax`. -/
theorem pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocalMax
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (x : X) (hx : x ∈ φ.source) :
    pathPrimitive h_conn x₀ om x
      = pathPrimitive h_conn x₀ om y
        + chartLocalPrimitiveMax φ h_max h_target_convex y hy om x hx := by
  -- α : x₀ ⇝ y via SmoothPathConnected (Classical.choose).
  set α : SmoothPath 𝓘(ℝ, ℂ) X := (h_conn x₀ y).choose with hα_def
  have hα_src : α.src = x₀ := (h_conn x₀ y).choose_spec.1
  have hα_tgt : α.tgt = y := (h_conn x₀ y).choose_spec.2
  -- β : y ⇝ x via linearInChartSegmentMax (chart-line).
  set β : SmoothPath 𝓘(ℝ, ℂ) X :=
    SmoothPath.linearInChartSegmentMax φ h_max y x hy hx
      (Convex.segment_subset h_target_convex
        (φ.map_source hy) (φ.map_source hx))
    with hβ_def
  have hβ_src : β.src = y :=
    SmoothPath.linearInChartSegmentMax_src φ h_max y x hy hx _
  have hβ_tgt : β.tgt = x :=
    SmoothPath.linearInChartSegmentMax_tgt φ h_max y x hy hx _
  -- Concatenation `γ := α ⋆ β : x₀ ⇝ x`.
  have h_concat_endpoint : α.tgt = β.src := hα_tgt.trans hβ_src.symm
  set γ : SmoothPath 𝓘(ℝ, ℂ) X := α.concat β h_concat_endpoint with hγ_def
  have hγ_src : γ.src = x₀ := by
    rw [hγ_def, SmoothPath.concat_src]; exact hα_src
  have hγ_tgt : γ.tgt = x := by
    rw [hγ_def, SmoothPath.concat_tgt]; exact hβ_tgt
  -- pathPrimitive om x = complexChainPeriod (single γ) om by path-independence.
  rw [pathPrimitive_eq_integral_of_loopPeriodVanishes
      h_conn x₀ om h_loop x γ hγ_src hγ_tgt]
  -- complexChainPeriod (single γ) om
  --   = complexChainPeriod (single α) om + complexChainPeriod (single β) om.
  rw [hγ_def, complexChainPeriod_single_concat α β h_concat_endpoint om]
  -- complexChainPeriod (single α) om = pathPrimitive om y by path-independence
  -- (α is a smooth path from x₀ to y).
  rw [← pathPrimitive_eq_integral_of_loopPeriodVanishes
      h_conn x₀ om h_loop y α hα_src hα_tgt]
  -- complexChainPeriod (single β) om = chartLocalPrimitiveMax(φ, y) om x by
  -- definitional unfolding of chartLocalPrimitiveMax.
  rfl

end JacobianChallenge

end
