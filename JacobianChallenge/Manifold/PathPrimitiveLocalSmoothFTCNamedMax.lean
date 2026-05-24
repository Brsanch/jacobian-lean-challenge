/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveSmoothnessFromChartLocalMax

set_option linter.unusedSectionVars false

/-! # Maximal-atlas named chart-local smoothness/FTC hypotheses and composition

Parallel to `PathPrimitiveLocalSmoothFTCNamed.lean` but parameterised by
`h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X` instead of
`h_atlas : φ ∈ atlas ℂ X`. Built on `chartLocalPrimitiveExtendMax` and
the Max regularity transfer bridges.

## What this file ships

* `ChartLocalPrimitiveSmoothExtMax` — Prop, smoothness of
  `chartLocalPrimitiveExtendMax(φ, y) om` on `φ.source`.
* `ChartLocalPrimitiveFTCMax` — Prop, FTC identity at every chart-source
  point.
* `pathPrimitive_contMDiffOn_source_of_ChartLocalPrimitiveSmoothExtMax`
  — the smoothness composition.
* `mfderiv_pathPrimitive_eq_eval_on_source_of_ChartLocalPrimitiveFTCMax`
  — the FTC composition.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Named hypothesis (max): `chartLocalPrimitiveExtendMax(φ, y) om` is
`ContMDiffOn ω` on `φ.source`.** -/
def ChartLocalPrimitiveSmoothExtMax
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : Prop :=
  ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
    (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om)
    φ.source

/-- **Named hypothesis (max): chart-local FTC at every chart-source point.** -/
def ChartLocalPrimitiveFTCMax
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : Prop :=
  ∀ (x : X) (hx : x ∈ φ.source),
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x

/-- **`pathPrimitive om` is `ContMDiffOn ω` on `φ.source` under
`LoopPeriodVanishes om x₀` + `ChartLocalPrimitiveSmoothExtMax`.** -/
theorem pathPrimitive_contMDiffOn_source_of_ChartLocalPrimitiveSmoothExtMax
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (h_smooth_ext :
      ChartLocalPrimitiveSmoothExtMax φ h_max h_target_convex y hy om) :
    ContMDiffOn (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om)
      φ.source := by
  intro x hx
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  have h_chart_at : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x :=
    (h_smooth_ext x hx).contMDiffAt (h_open.mem_nhds hx)
  have h_path_at :=
    pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtendMax_contMDiffAt
      h_conn x₀ om h_loop φ h_max h_target_convex y hy hx h_chart_at
  exact h_path_at.contMDiffWithinAt

/-- **`mfderiv pathPrimitive = om.eval` on `φ.source` under
`LoopPeriodVanishes om x₀` + `ChartLocalPrimitiveSmoothExtMax` +
`ChartLocalPrimitiveFTCMax`.** -/
theorem mfderiv_pathPrimitive_eq_eval_on_source_of_ChartLocalPrimitiveFTCMax
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (h_smooth_ext :
      ChartLocalPrimitiveSmoothExtMax φ h_max h_target_convex y hy om)
    (h_ftc_ext :
      ChartLocalPrimitiveFTCMax φ h_max h_target_convex y hy om)
    (x : X) (hx : x ∈ φ.source) :
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ om) x := by
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  have h_chart_at : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x :=
    (h_smooth_ext x hx).contMDiffAt (h_open.mem_nhds hx)
  have h_chart_diff : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x :=
    h_chart_at.mdifferentiableAt (by decide)
  rw [h_ftc_ext x hx]
  exact (mfderiv_pathPrimitive_eq_mfderiv_chartLocalPrimitiveExtendMax
    h_conn x₀ om h_loop φ h_max h_target_convex y hy hx h_chart_diff).symm

end JacobianChallenge

end
