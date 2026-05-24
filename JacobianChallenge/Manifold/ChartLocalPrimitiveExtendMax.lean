/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtend
import JacobianChallenge.Manifold.ChartLocalPrimitiveMax

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

The `pathPrimitive_*` bridge lemmas from `ChartLocalPrimitiveExtend.lean`
(`pathPrimitive_eqOn_chartLocalPrimitiveExtend_add_const` and
`pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at`)
consume `pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocal`
from `PathPrimitiveChartLocalBridge.lean`. That bridge is atlas-typed
and uses `SmoothPath.linearInChartSegment` (plus its `_src`/`_tgt`
identities) directly — porting it to the Max variant is a separate
cascade step. The Max forms of the `pathPrimitive_*` lemmas land
alongside that bridge port.

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

end JacobianChallenge

end
