/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitive
import JacobianChallenge.Manifold.SmoothPathLinearInChartMax

set_option linter.unusedSectionVars false

/-! # Maximal-atlas variant of `chartLocalPrimitive`

Parallel to `ChartLocalPrimitive.lean` but parameterised by
`h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X` instead of
`h_atlas : φ ∈ atlas ℂ X`. Built on top of
`SmoothPath.linearInChartSegmentMax`.

Motivation. The canonical `chartAt ℂ x` does not in general have convex
target on arbitrary X, so the `HasConvexChartAtTarget X` typeclass
cannot be instantiated on arbitrary X. The structural answer is
`convexBallChartAt x` (in `Manifold/ConvexBallChartAtMaximalAtlas.lean`),
which has convex target and lies in the **maximal** atlas, not the
underlying atlas. To consume `convexBallChartAt`-style charts the whole
chart-local primitive arc must be rebuilt with `h_max` in place of
`h_atlas`.

This file is step 1 of that cascade: the `data` definition
`chartLocalPrimitiveMax` plus the basepoint identity
`chartLocalPrimitiveMax_self`. Smoothness in `x` and FTC are handled by
later cascade steps (`ChartLocalPrimitiveExtendMax`,
`PathPrimitiveLocalSmoothFTCNamedMax`, etc.).

## What this file ships

* `chartLocalPrimitiveMax` — the data definition.
* `chartLocalPrimitiveMax_eq_chartLocalPrimitive` — equality with the
  atlas-parameterised original whenever `h_atlas` is available.
* `linearInChartSegmentMax_self_*` — basepoint-identity helpers
  (ambient constant, velocity zero, integrand zero, integrate zero).
* `chartLocalPrimitiveMax_self` — `F(x₀) = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-! ## The chart-local primitive function (maximal-atlas variant) -/

/-- **Maximal-atlas variant of `chartLocalPrimitive`.**

Identical construction to `chartLocalPrimitive`, with the
atlas-membership parameter replaced by maximal-atlas membership and
`linearInChartSegment` replaced by `linearInChartSegmentMax`. -/
noncomputable def chartLocalPrimitiveMax
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ φ.source) : ℂ :=
  complexChainPeriod
    (SmoothChain.single
      (SmoothPath.linearInChartSegmentMax φ h_max x₀ x hx₀ hx
        (Convex.segment_subset h_target_convex
          (φ.map_source hx₀) (φ.map_source hx))))
    om

/-- **Identification with the atlas-parameterised original.** When the
chart `φ` is in `atlas ℂ X` (and hence in the maximal atlas via
`subset_maximalAtlas`), the two primitives agree pointwise. Follows
from `SmoothPath.linearInChartSegmentMax_eq_linearInChartSegment`. -/
lemma chartLocalPrimitiveMax_eq_chartLocalPrimitive
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ φ.source) :
    chartLocalPrimitiveMax φ
        (IsManifold.subset_maximalAtlas (n := ⊤) h_atlas)
        h_target_convex x₀ hx₀ om x hx
      = chartLocalPrimitive φ h_atlas h_target_convex x₀ hx₀ om x hx := by
  unfold chartLocalPrimitiveMax chartLocalPrimitive
  rw [SmoothPath.linearInChartSegmentMax_eq_linearInChartSegment]

/-! ## Basepoint-identity helpers (maximal-atlas variant)

Parallel of `linearInChartSegment_self_*` in `ChartLocalPrimitive.lean`,
with `h_atlas` replaced by `h_max` and `linearInChartSegment` replaced
by `linearInChartSegmentMax`. Proof bodies are identical: the helpers
in the atlas version only consume `h_atlas` by passing it through to
`linearInChartSegment`; the SmoothPath operations (`ambient`,
`velocity`, `integrand`, `integrate`) are generic. -/

/-- **Ambient extension on `unitInterval` of `linearInChartSegmentMax x₀ x₀`
is constant at `x₀`.** -/
lemma linearInChartSegmentMax_self_ambient_eq_on_unitInterval
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    (s : unitInterval) :
    (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).ambient s.val
      = x₀ := by
  rw [SmoothPath.ambient_eq_on_unitInterval]
  show (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).toPath s
      = x₀
  show φ.symm (bumpedSegment (φ x₀) (φ x₀) s.val) = x₀
  rw [bumpedSegment_self]
  exact φ.left_inv hx₀

/-- **Ambient extension of `linearInChartSegmentMax x₀ x₀` is eventually
constant `x₀` near any `t ∈ Ioo 0 1`.** -/
lemma linearInChartSegmentMax_self_ambient_eventuallyEq_const
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).ambient
      =ᶠ[nhds t] (fun _ : ℝ => x₀) := by
  refine Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  have hs_unit : s ∈ unitInterval :=
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact linearInChartSegmentMax_self_ambient_eq_on_unitInterval
    φ h_max x₀ hx₀ h_seg ⟨s, hs_unit⟩

/-- **Velocity of `linearInChartSegmentMax x₀ x₀` vanishes on `Ioo 0 1`.** -/
lemma linearInChartSegmentMax_self_velocity_of_mem_Ioo
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).velocity t = 0 := by
  unfold SmoothPath.velocity
  have h_eq :
      mfderiv (𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
        (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).ambient t
        = mfderiv (𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) (fun _ : ℝ => x₀) t :=
    (linearInChartSegmentMax_self_ambient_eventuallyEq_const
      φ h_max x₀ hx₀ h_seg ht).mfderiv_eq
  rw [h_eq]
  have h_const :
      mfderiv (𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) (fun _ : ℝ => x₀) t
        = (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
              TangentSpace (𝓘(ℝ, ℂ)) ((fun _ : ℝ => x₀) t)) :=
    mfderiv_const
  rw [h_const]
  show ((0 : ℝ →L[ℝ]
      TangentSpace (𝓘(ℝ, ℂ)) ((fun _ : ℝ => x₀) t)) (1 : ℝ)) = 0
  exact ContinuousLinearMap.zero_apply (1 : ℝ)

/-- **Integrand of `linearInChartSegmentMax x₀ x₀` vanishes on `Ioo 0 1`.** -/
lemma linearInChartSegmentMax_self_integrand_of_mem_Ioo
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).integrand om t = 0 := by
  unfold SmoothPath.integrand
  rw [linearInChartSegmentMax_self_velocity_of_mem_Ioo φ h_max x₀ hx₀ h_seg ht]
  unfold SmoothPath.applyCotangent
  exact ContinuousLinearMap.map_zero _

/-- **Path integral of any smooth 1-form along `linearInChartSegmentMax x₀ x₀`
vanishes.** -/
theorem linearInChartSegmentMax_self_integrate
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    (SmoothPath.linearInChartSegmentMax φ h_max x₀ x₀ hx₀ hx₀ h_seg).integrate om = 0 := by
  unfold SmoothPath.integrate
  refine intervalIntegral.integral_zero_ae ?_
  have h_meas_zero : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
    Real.volume_singleton
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact h_meas_zero
  filter_upwards [h_almost] with x hx hx_Ι
  have h_uIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_Ι
    exact hx_Ι
  have h_Ioo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨h_uIoc.1, lt_of_le_of_ne h_uIoc.2 hx⟩
  exact linearInChartSegmentMax_self_integrand_of_mem_Ioo
    φ h_max x₀ hx₀ h_seg om h_Ioo

/-- **Basepoint identity for `chartLocalPrimitiveMax`.**
`F(x₀) = 0` — the chart-local primitive (maximal-atlas variant)
vanishes at the basepoint. -/
@[simp] theorem chartLocalPrimitiveMax_self
    (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (om : HolomorphicOneForm X) :
    chartLocalPrimitiveMax φ h_max h_target_convex x₀ hx₀ om x₀ hx₀ = 0 := by
  unfold chartLocalPrimitiveMax complexChainPeriod
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single]
  rw [linearInChartSegmentMax_self_integrate, linearInChartSegmentMax_self_integrate]
  push_cast
  ring

end JacobianChallenge

end
