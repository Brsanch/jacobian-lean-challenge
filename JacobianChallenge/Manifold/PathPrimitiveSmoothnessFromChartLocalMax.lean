/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveExtendMax

set_option linter.unusedSectionVars false

/-! # Maximal-atlas variant of `pathPrimitive` regularity transfer

Parallel to `PathPrimitiveSmoothnessFromChartLocal.lean` but parameterised
by `h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X` instead of
`h_atlas : φ ∈ atlas ℂ X`. Built on `chartLocalPrimitiveExtendMax` and
the Max form of the EventuallyEq bridge.

## What this file ships

* `pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtendMax_contMDiffAt`
  — transfer of `ContMDiffAt` regularity.
* `pathPrimitive_contMDiffAt_iff_chartLocalPrimitiveExtendMax_contMDiffAt`
  — biconditional version.
* `mfderiv_pathPrimitive_eq_mfderiv_chartLocalPrimitiveExtendMax` —
  `mfderiv pathPrimitive x = mfderiv chartLocalPrimitiveExtendMax x`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Transfer `ContMDiffAt` from `chartLocalPrimitiveExtendMax` to
`pathPrimitive`.** -/
theorem pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtendMax_contMDiffAt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source)
    (h_chart_smooth : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) x := by
  have h_const :
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    contMDiffAt_const
  have h_sum :
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun x' : X =>
          chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
            + pathPrimitive h_conn x₀ om y) x :=
    h_chart_smooth.add h_const
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtendMax_add_const_at
      h_conn x₀ om h_loop φ h_max h_target_convex y hy x hx
  exact h_sum.congr_of_eventuallyEq h_eq

/-- **Biconditional version using `Filter.EventuallyEq.contMDiffAt_iff`.** -/
theorem pathPrimitive_contMDiffAt_iff_chartLocalPrimitiveExtendMax_contMDiffAt
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) x ↔
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x := by
  refine ⟨fun h_path => ?_, fun h_chart =>
    pathPrimitive_contMDiffAt_of_chartLocalPrimitiveExtendMax_contMDiffAt
      h_conn x₀ om h_loop φ h_max h_target_convex y hy hx h_chart⟩
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtendMax_add_const_at
      h_conn x₀ om h_loop φ h_max h_target_convex y hy x hx
  have h_sum : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (fun x' : X =>
        chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y) x :=
    h_path.congr_of_eventuallyEq h_eq.symm
  have h_const :
      ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    contMDiffAt_const
  have h_diff := h_sum.sub h_const
  have h_funeq :
      (fun x' : X => (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y) - pathPrimitive h_conn x₀ om y)
      = chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om := by
    funext x'; ring
  rw [h_funeq] at h_diff
  exact h_diff

/-- **`mfderiv pathPrimitive = mfderiv chartLocalPrimitiveExtendMax` at a chart
point.** -/
theorem mfderiv_pathPrimitive_eq_mfderiv_chartLocalPrimitiveExtendMax
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (y : X) (hy : y ∈ φ.source)
    {x : X} (hx : x ∈ φ.source)
    (h_chart_diff : MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (pathPrimitive h_conn x₀ om) x
      = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om) x := by
  have h_eq :
      pathPrimitive h_conn x₀ om =ᶠ[nhds x]
        fun x' => chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y :=
    pathPrimitive_eventuallyEq_chartLocalPrimitiveExtendMax_add_const_at
      h_conn x₀ om h_loop φ h_max h_target_convex y hy x hx
  rw [h_eq.mfderiv_eq]
  have h_funeq :
      (fun x' : X =>
        chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om x'
          + pathPrimitive h_conn x₀ om y)
      = (chartLocalPrimitiveExtendMax φ h_max h_target_convex y hy om
          + fun _ : X => pathPrimitive h_conn x₀ om y) := rfl
  rw [h_funeq]
  have h_const_diff :
      MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (fun _ : X => pathPrimitive h_conn x₀ om y) x :=
    mdifferentiableAt_const
  rw [mfderiv_add h_chart_diff h_const_diff, mfderiv_const]
  exact add_zero _

end JacobianChallenge

end
