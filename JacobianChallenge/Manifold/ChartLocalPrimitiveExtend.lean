/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveChartLocalBridge

set_option linter.unusedSectionVars false

/-! # `chartLocalPrimitive` as a function `X → ℂ` (extension by zero)

`chartLocalPrimitive φ h_atlas h_target_convex y hy om` is naturally a
"function with a membership proof" — its signature is

  `(x : X) → x ∈ φ.source → ℂ`.

To talk about `ContMDiff`/`ContMDiffOn` regularity in the standard
mathlib API (which wants `f : X → ℂ`), we wrap it as a total function
`X → ℂ` that agrees with `chartLocalPrimitive` on `φ.source` and is
zero off `φ.source`. The wrapping is via `dite` on the chart-membership
proposition.

## What this file ships

* `chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om : X → ℂ`
  — the total-function wrapper.
* `chartLocalPrimitiveExtend_eq_chartLocalPrimitive` — agreement on
  `φ.source`.
* `pathPrimitive_eqOn_chartLocalPrimitiveExtend_add_const` —
  under `LoopPeriodVanishes om x₀`, `pathPrimitive om` agrees with
  `chartLocalPrimitiveExtend (φ, y) om + pathPrimitive om y` on
  `φ.source`. Direct corollary of
  `pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocal`.
* `pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at`
  — the `EventuallyEq` version at a single point of `φ.source` (uses
  openness of `φ.source` via `φ.open_source`). Smoothness/derivative
  transfer to `pathPrimitive` from `chartLocalPrimitiveExtend` follows
  via `Filter.EventuallyEq.contMDiffAt_iff` and
  `Filter.EventuallyEq.mfderiv_eq` (separate chip).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Classical

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Extension of `chartLocalPrimitive` to a total function `X → ℂ`.**

Equals `chartLocalPrimitive φ h_atlas h_target_convex y hy om x hx` for
`x ∈ φ.source`; zero off `φ.source`. Defined via `dite` on the chart-
membership proposition. -/
noncomputable def chartLocalPrimitiveExtend
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X) : X → ℂ :=
  fun x =>
    if hx : x ∈ φ.source then
      chartLocalPrimitive φ h_atlas h_target_convex y hy om x hx
    else 0

/-- **Agreement on `φ.source`.** -/
lemma chartLocalPrimitiveExtend_eq_chartLocalPrimitive
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ φ.source) :
    chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x
      = chartLocalPrimitive φ h_atlas h_target_convex y hy om x hx := by
  unfold chartLocalPrimitiveExtend
  rw [dif_pos hx]

/-- **Vanishing off `φ.source`.** -/
lemma chartLocalPrimitiveExtend_eq_zero_of_notMem
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∉ φ.source) :
    chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x = 0 := by
  unfold chartLocalPrimitiveExtend
  exact dif_neg hx

/-- **Set-level identity: `pathPrimitive` agrees with
`chartLocalPrimitiveExtend + pathPrimitive y` on `φ.source`.** Direct
restriction of the bridge. -/
theorem pathPrimitive_eqOn_chartLocalPrimitiveExtend_add_const
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source) :
    EqOn (pathPrimitive h_conn x₀ om)
      (fun x => chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x
        + pathPrimitive h_conn x₀ om y)
      φ.source := by
  intro x hx
  show pathPrimitive h_conn x₀ om x
    = chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x
      + pathPrimitive h_conn x₀ om y
  rw [chartLocalPrimitiveExtend_eq_chartLocalPrimitive
      φ h_atlas h_target_convex y hy om x hx,
    pathPrimitive_eq_pathPrimitive_at_chartBase_add_chartLocal
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy x hx]
  ring

/-- **`EventuallyEq` version at a point of `φ.source`.** Uses
`φ.open_source` to upgrade the set-level `EqOn` to an `EventuallyEq` in
the neighborhood filter at `x`. -/
theorem pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    (x : X) (hx : x ∈ φ.source) :
    pathPrimitive h_conn x₀ om =ᶠ[nhds x]
      fun x' => chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
        + pathPrimitive h_conn x₀ om y := by
  have h_open : IsOpen (φ.source : Set X) := φ.open_source
  refine Filter.eventually_of_mem (h_open.mem_nhds hx) ?_
  intro x' hx'
  exact pathPrimitive_eqOn_chartLocalPrimitiveExtend_add_const
    h_conn x₀ om h_loop φ h_atlas h_target_convex y hy hx'

end JacobianChallenge

end
