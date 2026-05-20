/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtend

set_option linter.unusedSectionVars false

/-! # Transfer `ContMDiffAt` / `mfderiv` of `pathPrimitive` from `chartLocalPrimitiveExtend`

Under `LoopPeriodVanishes om x₀`, the bridge from
`ChartLocalPrimitiveExtend.lean` gives
`pathPrimitive om =ᶠ[nhds x] chartLocalPrimitiveExtend(φ, y) om + const`
for every `x` in a chart `φ` containing the chart-basepoint `y`. The
right-hand side is the *explicit chart-line* primitive, parameterised
by the smooth bumped affine segment in chart coordinates — so smoothness
in the endpoint is amenable to mathlib's
`ParametricIntervalIntegral` machinery (work in progress in
`ChartLocalPrimitiveSmoothness.lean`).

This file transfers smoothness/`mfderiv` properties of
`chartLocalPrimitiveExtend` *at a point* to `pathPrimitive` *at the same
point*, via `Filter.EventuallyEq.contMDiffAt_iff` and
`Filter.EventuallyEq.mfderiv_eq`. The constant offset is absorbed via
`contMDiffAt_const` and `mfderiv_const`.

## What this file ships

* `pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtend_contMDiffAt`
  — transfer of `ContMDiffAt` regularity.
* `pathPrimitive_contMDiffAt_iff_chartLocalPrimitiveExtend_contMDiffAt`
  — biconditional version (using
  `Filter.EventuallyEq.contMDiffAt_iff`).
* `mfderiv_pathPrimitive_eq_mfderiv_chartLocalPrimitiveExtend` —
  `mfderiv pathPrimitive x = mfderiv chartLocalPrimitiveExtend x` (the
  constant offset has zero derivative).

These compose with future chart-local smoothness/FTC theorems to give
unconditional smoothness/FTC of `pathPrimitive` on `φ.source` (under
`LoopPeriodVanishes`).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Transfer `ContMDiffAt` from `chartLocalPrimitiveExtend` to
`pathPrimitive`.**

If `chartLocalPrimitiveExtend(φ, y) om` is `ContMDiffAt ω` at a point
`x ∈ φ.source`, then `pathPrimitive h_conn x₀ om` is also `ContMDiffAt ω`
at `x`. Proof: the two differ by an additive constant on a
neighborhood of `x` (the bridge from
`ChartLocalPrimitiveExtend.lean`), so `ContMDiffAt` propagates via the
sum-of-`ContMDiffAt`-with-`ContMDiffAt_const` plus
`congr_of_eventuallyEq`. -/
theorem pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtend_contMDiffAt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source)
    (h_chart_smooth : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) x := by
  -- The constant `pathPrimitive om y` is ContMDiffAt at any point.
  have h_const :
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    contMDiffAt_const
  -- Sum of ContMDiffAt is ContMDiffAt.
  have h_sum :
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun x' : X =>
          chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
            + pathPrimitive h_conn x₀ om y) x :=
    h_chart_smooth.add h_const
  -- pathPrimitive =ᶠ chartLocalPrimitiveExtend + const at x.
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy x hx
  exact h_sum.congr_of_eventuallyEq h_eq

/-- **Biconditional version using `Filter.EventuallyEq.contMDiffAt_iff`.** -/
theorem pathPrimitive_contMDiffAt_iff_chartLocalPrimitiveExtend_contMDiffAt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) x ↔
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x := by
  refine ⟨fun h_path => ?_, fun h_chart =>
    pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtend_contMDiffAt
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy hx h_chart⟩
  -- Reverse direction: pathPrimitive = (extend + const), so extend = pathPrimitive - const.
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy x hx
  -- (extend + const) is ContMDiffAt at x.
  have h_sum : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (fun x' : X =>
        chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y) x :=
    h_path.congr_of_eventuallyEq h_eq.symm
  -- Subtract the constant.
  have h_const :
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    contMDiffAt_const
  -- chartLocalPrimitiveExtend = (extend + const) - const.
  have h_diff := h_sum.sub h_const
  -- The difference is exactly chartLocalPrimitiveExtend.
  have h_funeq :
      (fun x' : X => (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y) - pathPrimitive h_conn x₀ om y)
      = chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om := by
    funext x'; ring
  rw [h_funeq] at h_diff
  exact h_diff

/-- **`mfderiv pathPrimitive = mfderiv chartLocalPrimitiveExtend` at a chart
point.** The constant offset has zero `mfderiv` and drops out. -/
theorem mfderiv_pathPrimitive_eq_mfderiv_chartLocalPrimitiveExtend
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source)
    (h_chart_diff : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (pathPrimitive h_conn x₀ om) x
      = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om) x := by
  -- pathPrimitive =ᶠ chartLocalPrimitiveExtend + const at x.
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtend_add_const_at
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy x hx
  rw [h_eq.mfderiv_eq]
  -- The eta-expanded lambda is definitionally `(extend) + (const)`.
  have h_funeq :
      (fun x' : X =>
        chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y)
      = (chartLocalPrimitiveExtend φ h_atlas h_target_convex y hy om
          + fun _ : X => pathPrimitive h_conn x₀ om y) := rfl
  rw [h_funeq]
  -- mfderiv (extend + const) x = mfderiv extend x + mfderiv const x.
  have h_const_diff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    mdifferentiableAt_const
  rw [mfderiv_add h_chart_diff h_const_diff, mfderiv_const]
  exact add_zero _

end JacobianChallenge

end
