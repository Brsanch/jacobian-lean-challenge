/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JacobianChallenge.Manifold.SmoothPathConst
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # The constant-path integral vanishes

For any smooth 1-form `ω`, the path integral of `ω` along the constant
smooth path at any point `P : X` is zero:

    `(SmoothPath.const I X P).integrate ω = 0`.

## Strategy

The `SmoothPath.const I X P` is built with `Path.refl P` as the
underlying continuous path. Any ambient C^∞ extension `f : ℝ → X`
witnessing its smoothness must satisfy `f t.val = P` for
`t ∈ unitInterval` (by the `ambient_eq_on_unitInterval` projection of
the structure's smoothness field). Hence `γ.ambient` is constantly
`P` on the closed unit interval `[0, 1]`.

Mathematically:

1. On the open interval `(0, 1)`, `γ.ambient =ᶠ[𝓝 t] (fun _ ↦ P)`
   for every `t ∈ (0, 1)` (the neighborhood `(0, 1)` itself
   witnesses this).
2. Hence `mfderiv γ.ambient t = mfderiv (const P) t = 0`
   (`Filter.EventuallyEq.mfderiv_eq` + `mfderiv_const`).
3. Hence `γ.velocity t = (mfderiv …) 1 = 0`.
4. Hence `γ.integrand ω t = applyCotangent (ω (γ.ambient t)) 0 = 0`
   (continuous-linear-map zero application).
5. Hence the integrand is zero on the co-null set `(0, 1) ⊂ [0, 1]`.
6. The interval integral over `[0, 1]` of a function that is zero
   almost everywhere is zero.

## What this file delivers

* `SmoothPath.const_velocity_of_mem_Ioo` — for `t ∈ Ioo 0 1`,
  `(SmoothPath.const I X P).velocity t = 0`.
* `SmoothPath.const_integrand_of_mem_Ioo` — for `t ∈ Ioo 0 1`,
  `(SmoothPath.const I X P).integrand ω t = 0`.
* `SmoothPath.integrate_const` — `(SmoothPath.const I X P).integrate
  ω = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter Topology JacobianChallenge
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-- **The constant-path ambient is constant on `[0, 1]`.** Any
ambient witness `f : ℝ → X` of `(SmoothPath.const I X P)`'s
smoothness satisfies `f s = P` for every `s ∈ unitInterval`. -/
lemma const_ambient_eq_of_mem_unitInterval (P : X) (s : ℝ)
    (hs : s ∈ unitInterval) :
    (SmoothPath.const I X P).ambient s = P := by
  have h_eq := (SmoothPath.const I X P).ambient_eq_on_unitInterval ⟨s, hs⟩
  -- `h_eq : ambient ⟨s, hs⟩.val = toPath ⟨s, hs⟩`. RHS = `Path.refl P ⟨s, hs⟩ = P`.
  show (SmoothPath.const I X P).ambient s = P
  have h_val : (⟨s, hs⟩ : unitInterval).val = s := rfl
  rw [h_val] at h_eq
  rw [h_eq]
  -- Goal: `(SmoothPath.const I X P).toPath ⟨s, hs⟩ = P`. Underlying is `Path.refl P`.
  rfl

/-- **The constant-path ambient equals the constant function on the
open neighborhood `(0, 1)` of any `t ∈ (0, 1)`.** -/
lemma const_ambient_eventuallyEq_const (P : X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.const I X P).ambient =ᶠ[𝓝 t] (fun _ : ℝ => P) := by
  -- The open interval `Ioo 0 1` is an open set containing `t`. On
  -- `Ioo 0 1 ⊆ unitInterval`, the constant-path ambient equals `P`.
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  -- `hs : s ∈ Ioo 0 1`, so `s ∈ unitInterval = Icc 0 1`.
  have hs_unit : s ∈ unitInterval :=
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact const_ambient_eq_of_mem_unitInterval P s hs_unit

/-- **The constant-path velocity vanishes on `(0, 1)`.** -/
lemma const_velocity_of_mem_Ioo (P : X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.const I X P).velocity t = 0 := by
  unfold velocity
  -- `mfderiv γ.ambient t = mfderiv (const P) t = 0` by
  -- `Filter.EventuallyEq.mfderiv_eq` + `mfderiv_const`.
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I (SmoothPath.const I X P).ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I (fun _ : ℝ => P) t :=
    (const_ambient_eventuallyEq_const P ht).mfderiv_eq
  rw [h_eq]
  -- `mfderiv (const P) t = 0`, so `0 (1) = 0`.
  have h_const : mfderiv (𝓘(ℝ, ℝ)) I (fun _ : ℝ => P) t
      = (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
            TangentSpace I ((fun _ : ℝ => P) t)) :=
    mfderiv_const
  rw [h_const]
  -- Now the goal is `(0 : ℝ →L[ℝ] _) 1 = 0`. Reduces to `(0 : _) (1 : ℝ) = 0`.
  show ((0 : ℝ →L[ℝ] TangentSpace I ((fun _ : ℝ => P) t)) (1 : ℝ)) = 0
  exact ContinuousLinearMap.zero_apply (1 : ℝ)

/-- **The constant-path integrand vanishes on `(0, 1)`.** -/
lemma const_integrand_of_mem_Ioo (P : X) (ω : SmoothOneForm I X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (SmoothPath.const I X P).integrand ω t = 0 := by
  unfold integrand
  rw [const_velocity_of_mem_Ioo P ht]
  -- Goal: `applyCotangent (ω (γ.ambient t)) 0 = 0`.
  unfold applyCotangent
  exact ContinuousLinearMap.map_zero _

/-- **The constant-path integral vanishes.** For any smooth 1-form
`ω` and any point `P : X`, the path integral of `ω` along the
constant smooth path at `P` is zero.

The integrand is zero on `Ioo 0 1` (`const_integrand_of_mem_Ioo`).
On `Ι 0 1 = Ioc 0 1`, the integrand is zero a.e. (the singleton
`{1}` has Lebesgue measure zero). Hence the interval integral is
zero by `intervalIntegral.integral_zero_ae`. -/
theorem integrate_const (P : X) (ω : SmoothOneForm I X) :
    (SmoothPath.const I X P).integrate ω = 0 := by
  unfold integrate
  refine intervalIntegral.integral_zero_ae ?_
  -- Goal: `∀ᵐ x ∂volume, x ∈ Ι 0 1 → integrand x = 0`.
  -- `Ι 0 1 = Ioc 0 1` (since `0 ≤ 1`). On `Ioc 0 1`, the set where
  -- the integrand is nonzero is contained in `{1}`, which has
  -- volume zero. Use `MeasureTheory.ae_iff` plus the singleton-null
  -- fact.
  have h_meas_zero : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
    Real.volume_singleton
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact h_meas_zero
  filter_upwards [h_almost] with x hx hx_Ι
  -- `hx : x ≠ 1`, `hx_Ι : x ∈ Ι 0 1 = Ioc 0 1`.
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_Ι
  -- `hx_Ι : x ∈ Ioc 0 1`. Combined with `x ≠ 1`, get `x ∈ Ioo 0 1`.
  exact const_integrand_of_mem_Ioo P ω
    ⟨hx_Ι.1, lt_of_le_of_ne hx_Ι.2 hx⟩

end SmoothPath

end
