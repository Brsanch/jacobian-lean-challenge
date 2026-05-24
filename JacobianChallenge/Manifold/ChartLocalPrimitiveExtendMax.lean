/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtend
import JacobianChallenge.Manifold.ChartLocalPrimitiveMax
import JacobianChallenge.Manifold.PathPrimitiveChartLocalBridgeMax

set_option linter.unusedSectionVars false

/-! # `chartLocalPrimitiveMax` as a function `X → ℂ` (extension by zero)

Maximal-atlas variant of `ChartLocalPrimitiveExtend.lean`. Same
`dite`-based total-function wrapping pattern, built on
`chartLocalPrimitiveMax` and the maximal-atlas membership parameter
`h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X`.

## What this file ships

* `chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om : X → ℂ`
  — the total-function wrapper around `chartLocalPrimitiveMax`.
* `chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax` — agreement
  on `φ.source`.
* `chartLocalPrimitiveExtendMax_eq_zero_of_notMem` — vanishing off
  `φ.source`.
* `chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveExtend` —
  agreement with the atlas-parameterised original whenever `h_atlas`
  is available (i.e. equal as functions `X → ℂ`).
* `pathPrimitive_eqOn_chartLocalPrimitiveExtendMax_add_const` and
  `pathPrimitive_eventuallyEq_chartLocalPrimitiveExtendMax_add_const_at`
  — the `EqOn` and `EventuallyEq` forms of the Max bridge, mirrors of
  the atlas lemmas in `ChartLocalPrimitiveExtend.lean`, consuming the
  bridge `pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocalMax`
  from `PathPrimitiveChartLocalBridgeMax.lean`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Classical

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Maximal-atlas variant of `chartLocalPrimitiveExtend`.**

Equals `chartLocalPrimitiveMax φ h_max h_target_convex y hy om x hx`
for `x ∈ φ.source`; zero off `φ.source`. -/
noncomputable def chartLocalPrimitiveExtendMax
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : X → ℂ :=
  fun x =>
    if hx : x ∈ φ.source then
      chartLocalPrimitiveMax φ h_max h_target_convex y hy om x hx
    else 0

/-- **Agreement on `φ.source`.** -/
lemma chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ φ.source) :
    chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x
      = chartLocalPrimitiveMax φ h_max h_target_convex y hy om x hx := by
  unfold chartLocalPrimitiveExtendMax
  rw [dif_pos hx]

/-- **Vanishing off `φ.source`.** -/
lemma chartLocalPrimitiveExtendMax_eq_zero_of_notMem
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∉ φ.source) :
    chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x = 0 := by
  unfold chartLocalPrimitiveExtendMax
  exact dif_neg hx

/-- **Identification with the atlas-parameterised original.** When the
chart `φ` is in `atlas ℂ X` (hence in the maximal atlas via
`subset_maximalAtlas`), the two total-function wrappers are equal as
functions `X → ℂ`. Follows pointwise from
`chartLocalPrimitiveMax_eq_chartLocalPrimitive`. -/
lemma chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveExtend
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) :
    chartLocalPrimitiveExtendMax φ
        (IsManifold.subset_maximalAtlas (n := ⊤) h_atlas)
        h_target_convex y hy om
      = chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om := by
  funext x
  unfold chartLocalPrimitiveExtendMax chartLocalPrimitiveExtend
  by_cases hx : x ∈ φ.source
  · rw [dif_pos hx, dif_pos hx,
      chartLocalPrimitiveMax_eq_chartLocalPrimitive
        φ h_atlas h_target_convex y hy om x hx]
  · rw [dif_neg hx, dif_neg hx]

/-- **Set-level identity: `pathPrimitive` agrees with
`chartLocalPrimitiveExtendMax + pathPrimitive y` on `φ.source`.**
Maximal-atlas form of `pathPrimitive_eqOn_chartLocalPrimitiveExtend_add_const`.
Direct restriction of `pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocalMax`. -/
theorem pathPrimitive_eqOn_chartLocalPrimitiveExtendMax_add_const
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source) :
    EqOn (pathPrimitive h_conn x₀ om)
      (fun x => chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x
        + pathPrimitive h_conn x₀ om y)
      φ.source := by
  intro x hx
  show pathPrimitive h_conn x₀ om x
    = chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x
      + pathPrimitive h_conn x₀ om y
  rw [chartLocalPrimitiveExtendMax_eq_chartLocalPrimitiveMax
      φ h_max h_target_convex y hy om x hx,
    pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocalMax
      h_conn x₀ om h_loop φ h_max h_target_convex y hy x hx]
  ring

/-- **`EventuallyEq` version at a point of `φ.source`.** Maximal-atlas
form of `pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at`.
Uses `φ.open_source` to upgrade the set-level `EqOn` to an
`EventuallyEq` in the neighborhood filter at `x`. -/
theorem pathPrimitive_eventuallyEq_chartLocalPrimitiveExtendMax_add_const_at
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (x : X) (hx : x ∈ φ.source) :
    pathPrimitive h_conn x₀ om =ᶠ[nhds x]
      fun x' => chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
        + pathPrimitive h_conn x₀ om y := by
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  refine Filter.eventually_of_mem (h_open.mem_nhds hx) ?_
  intro x' hx'
  exact pathPrimitive_eqOn_chartLocalPrimitiveExtendMax_add_const
    h_conn x₀ om h_loop φ h_max h_target_convex y hy hx'

end JacobianChallenge

end
