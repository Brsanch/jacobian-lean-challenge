/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexChainPeriodFormLinear
import JacobianChallenge.Manifold.SmoothPathIntegrateConst
import JacobianChallenge.Manifold.SmoothPathLinearInChart

/-! # Chart-local primitive of a holomorphic 1-form

For a chart `φ : OpenPartialHomeomorph X ℂ` with convex target and a
fixed basepoint `x₀ ∈ φ.source`, the *chart-local primitive* of a
holomorphic 1-form `om : HolomorphicOneForm X` is

  `F(x) := complexChainPeriod (single γ_{x₀, x}) om`

where `γ_{x₀, x}` is the smooth path constructed by
`SmoothPath.linearInChartSegment φ x₀ x` (the C^∞-bumped affine segment
in chart coordinates, well-defined because the chart target is convex
and so contains the segment from `φ x₀` to `φ x`).

This file ships the **data definition** of `chartLocalPrimitive` plus
the **basepoint identity** `F(x₀) = 0`. The basepoint identity follows
from the fact that the smooth path from `x₀` to `x₀` constructed by
`linearInChartSegment` has constant ambient extension `x₀` on
`unitInterval` (because `bumpedSegment a a t = a`), hence zero velocity
on `Ioo 0 1`, hence zero integrand a.e., hence zero integral.

Smoothness of `F` in the endpoint `x` (the substantive "E" content of
the primitive-existence arc) and the FTC identity `mfderiv F = om.eval`
("F" content) are deferred to subsequent chips. They use parameter-
dependent integral smoothness from mathlib's `ParametricIntervalIntegral`
+ chart-pullback joint smoothness of
`(z, t) ↦ φ.symm (bumpedSegment (φ x₀) z t)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology Bundle ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-! ## Helper: `bumpedSegment a a t = a` -/

/-- The bumped affine segment with coinciding endpoints `a = b` is the
constant function at `a`. Algebraic identity:
`(1 - σ) • a + σ • a = ((1 - σ) + σ) • a = 1 • a = a`. -/
@[simp] lemma bumpedSegment_self (a : ℂ) (t : ℝ) :
    bumpedSegment a a t = a := by
  show (1 - Real.smoothTransition t) • a + Real.smoothTransition t • a = a
  -- Reduce ℝ-smul to ℂ-multiplication, then ring.
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-! ## The chart-local primitive function -/

/-- **Chart-local primitive of a holomorphic 1-form at basepoint `x₀`.**
For `x ∈ φ.source`, defines

    `F(x) := complexChainPeriod (single γ_{x₀, x}) om`

where `γ_{x₀, x} = SmoothPath.linearInChartSegment φ h_atlas x₀ x` is
the C^∞-bumped affine segment in chart coordinates. The convexity of
`φ.target` ensures the segment `[φ x₀, φ x]` lies in the target, which
is the precondition of `linearInChartSegment`.

The candidate `F` for the primitive of `om` is a function on
`φ.source ⊆ X`. Smoothness in `x` is the substantive E-content of the
primitive-existence arc (deferred to a subsequent chip via parameter-
dependent integral smoothness). -/
noncomputable def chartLocalPrimitive
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (om : HolomorphicOneForm X)
    (x : X) (hx : x ∈ φ.source) : ℂ :=
  complexChainPeriod
    (SmoothChain.single
      (SmoothPath.linearInChartSegment φ h_atlas x₀ x hx₀ hx
        (Convex.segment_subset h_target_convex
          (φ.map_source hx₀) (φ.map_source hx))))
    om

/-! ## Basepoint identity `F(x₀) = 0`

The path `γ_{x₀, x₀}` has constant ambient extension at `x₀` (because
`bumpedSegment (φ x₀) (φ x₀) t = φ x₀`, and `φ.symm (φ x₀) = x₀`).
Hence its velocity is zero on `Ioo 0 1`, its integrand against any
1-form is zero on `Ioo 0 1`, and its `SmoothPath.integrate` is zero by
`intervalIntegral.integral_zero_ae`. The
`complexChainPeriod (single _) om` then collapses to zero on both real
and imaginary components, by the form-side zero identity.

We expose the chain in three steps so that subsequent chips can reuse
the ambient-and-velocity identities. -/

/-- **Ambient extension on `unitInterval` of `linearInChartSegment x₀ x₀`
is constant at `x₀`.** Via `ambient_eq_on_unitInterval` and
`bumpedSegment_self`. -/
lemma linearInChartSegment_self_ambient_eq_on_unitInterval
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    (s : unitInterval) :
    (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).ambient s.val
      = x₀ := by
  rw [SmoothPath.ambient_eq_on_unitInterval]
  show (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).toPath s
      = x₀
  -- Underlying toPath at s is `φ.symm (bumpedSegment (φ x₀) (φ x₀) s.val) = φ.symm (φ x₀) = x₀`.
  show φ.symm (bumpedSegment (φ x₀) (φ x₀) s.val) = x₀
  rw [bumpedSegment_self]
  exact φ.left_inv hx₀

/-- **Ambient extension of `linearInChartSegment x₀ x₀` is eventually
equal to the constant function `x₀` near any `t ∈ Ioo 0 1`.** Strict
analog of `const_ambient_eventuallyEq_const` for our linear-in-chart
segment with coinciding endpoints. -/
lemma linearInChartSegment_self_ambient_eventuallyEq_const
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).ambient
      =ᶠ[nhds t] (fun _ : ℝ => x₀) := by
  refine Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  have hs_unit : s ∈ unitInterval :=
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact linearInChartSegment_self_ambient_eq_on_unitInterval
    φ h_atlas x₀ hx₀ h_seg ⟨s, hs_unit⟩

/-- **Velocity of `linearInChartSegment x₀ x₀` vanishes on `Ioo 0 1`.**
Via `mfderiv_const` after recognising the ambient as eventually
constant. -/
lemma linearInChartSegment_self_velocity_of_mem_Ioo
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).velocity t = 0 := by
  unfold SmoothPath.velocity
  have h_eq :
      mfderiv (𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ)
        (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).ambient t
        = mfderiv (𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) (fun _ : ℝ => x₀) t :=
    (linearInChartSegment_self_ambient_eventuallyEq_const
      φ h_atlas x₀ hx₀ h_seg ht).mfderiv_eq
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

/-- **Integrand of `linearInChartSegment x₀ x₀` vanishes on `Ioo 0 1`.**
Pairing of the cotangent functional with the zero velocity. -/
lemma linearInChartSegment_self_integrand_of_mem_Ioo
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).integrand om t = 0 := by
  unfold SmoothPath.integrand
  rw [linearInChartSegment_self_velocity_of_mem_Ioo φ h_atlas x₀ hx₀ h_seg ht]
  unfold SmoothPath.applyCotangent
  exact ContinuousLinearMap.map_zero _

/-- **Path integral of any smooth 1-form along `linearInChartSegment x₀ x₀`
vanishes.** The integrand is zero on `Ioo 0 1`; the singleton `{1}` has
Lebesgue measure zero; hence the integrand is zero a.e. on `Ι 0 1` and
the interval integral is zero. Mirror of `SmoothPath.integrate_const`. -/
theorem linearInChartSegment_self_integrate
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (h_seg : segment ℝ (φ x₀) (φ x₀) ⊆ φ.target)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    (SmoothPath.linearInChartSegment φ h_atlas x₀ x₀ hx₀ hx₀ h_seg).integrate om = 0 := by
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
  -- hx_Ι : x ∈ Ι 0 1 = Ioc 0 1; hx : x ≠ 1.
  -- Combined: x ∈ Ioo 0 1.
  have h_uIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_Ι
    exact hx_Ι
  have h_Ioo : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨h_uIoc.1, lt_of_le_of_ne h_uIoc.2 hx⟩
  exact linearInChartSegment_self_integrand_of_mem_Ioo
    φ h_atlas x₀ hx₀ h_seg om h_Ioo

/-- **Basepoint identity for `chartLocalPrimitive`.**
`F(x₀) = 0` — the chart-local primitive vanishes at the basepoint.

Combines `linearInChartSegment_self_integrate` for both
`realComponent om` and `imagComponent om`, then collapses
`complexChainPeriod` via the form-side zero identity. -/
@[simp] theorem chartLocalPrimitive_self
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target)
    (x₀ : X) (hx₀ : x₀ ∈ φ.source)
    (om : HolomorphicOneForm X) :
    chartLocalPrimitive φ h_atlas h_target_convex x₀ hx₀ om x₀ hx₀ = 0 := by
  unfold chartLocalPrimitive complexChainPeriod
  -- The single-chain integrate collapses to the path integrate.
  rw [SmoothChain.integrate_single, SmoothChain.integrate_single]
  -- Both real- and imag-component integrals are zero along the constant path.
  rw [linearInChartSegment_self_integrate, linearInChartSegment_self_integrate]
  push_cast
  ring

end JacobianChallenge

end
