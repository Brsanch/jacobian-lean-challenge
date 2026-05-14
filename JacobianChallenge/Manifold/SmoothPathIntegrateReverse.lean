/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JacobianChallenge.Manifold.SmoothPathReverse
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option linter.unusedSectionVars false

/-! # `SmoothPath.reverse.integrate = -SmoothPath.integrate`

The reverse-path integral identity: for any smooth path `γ` and
smooth 1-form `ω`,

    `(γ.reverse).integrate ω = -(γ.integrate ω)`.

## Strategy

1. Show that on `s ∈ unitInterval = [0, 1]`, `(γ.reverse).ambient s
   = γ.ambient (1 - s)`. Both equal `γ.toPath.symm` at `s`, via
   `ambient_eq_on_unitInterval` applied to either path; mathlib's
   `Path.symm` formula `γ.symm s = γ ⟨1 - s.val, _⟩` provides the
   bridge.

2. Hence on the open interior `Ioo 0 1`, `(γ.reverse).ambient
   =ᶠ[𝓝 t] (fun s ↦ γ.ambient (1 - s))`.

3. The chain rule (`mfderiv_comp_apply`) plus the basic
   `mfderiv (fun s : ℝ ↦ 1 - s) t = -ContinuousLinearMap.id ℝ ℝ`
   (via `mfderiv_eq_fderiv` and the fderiv subtraction rule)
   yield the velocity identity
   `(γ.reverse).velocity t = -(γ.velocity (1 - t))` on `Ioo 0 1`.

4. The integrand identity follows by `applyCotangent` linearity.

5. The integral identity follows from
   `intervalIntegral.integral_comp_sub_left` (the substitution
   `t ↦ 1 - t` on `[0, 1]` is an involution that preserves the
   measure).

## What this file delivers

* `SmoothPath.reverseAmbient_eq_on_unitInterval` — pointwise
  identity on `[0, 1]`.
* `SmoothPath.reverseAmbient_eventuallyEq` — on `Ioo 0 1`, the
  Classical-chosen ambient of the reverse equals the explicit
  reverse-formula in a neighborhood.
* `SmoothPath.mfderiv_one_sub_apply_one` — chart-derivative of
  `1 - ·` at any `t` applied to `1` is `-1`.
* `SmoothPath.velocity_reverse_of_mem_Ioo` — velocity identity.
* `SmoothPath.integrand_reverse_of_mem_Ioo` — integrand identity.
* `SmoothPath.integrate_reverse` — `(γ.reverse).integrate ω
  = -(γ.integrate ω)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Pointwise reverse-ambient identity on `[0, 1]` -/

/-- **The reverse's ambient equals `γ.ambient (1 - s)` on `[0, 1]`.**
Both sides equal `γ.toPath.symm` applied at the appropriate
`unitInterval` point via `ambient_eq_on_unitInterval`. -/
lemma reverseAmbient_eq_on_unitInterval (γ : SmoothPath I X) (s : ℝ)
    (hs : s ∈ unitInterval) :
    γ.reverse.ambient s = γ.ambient (1 - s) := by
  -- `(γ.reverse).ambient s = (γ.reverse).toPath ⟨s, hs⟩ = γ.toPath.symm ⟨s, hs⟩
  --   = γ.toPath ⟨1 - s, _⟩ = γ.ambient (1 - s)`.
  have h_rev := γ.reverse.ambient_eq_on_unitInterval ⟨s, hs⟩
  have h_rev_val : (⟨s, hs⟩ : unitInterval).val = s := rfl
  rw [h_rev_val] at h_rev
  -- `h_rev : γ.reverse.ambient s = (γ.reverse).toPath ⟨s, hs⟩`.
  -- `(γ.reverse).toPath = γ.toPath.symm`, so RHS = `γ.toPath ⟨1 - s, _⟩`.
  have h_one_sub_unit : 1 - s ∈ unitInterval :=
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h_fwd := γ.ambient_eq_on_unitInterval ⟨1 - s, h_one_sub_unit⟩
  have h_fwd_val : (⟨1 - s, h_one_sub_unit⟩ : unitInterval).val = 1 - s := rfl
  rw [h_fwd_val] at h_fwd
  -- `h_fwd : γ.ambient (1 - s) = γ.toPath ⟨1 - s, _⟩`.
  rw [h_rev, h_fwd]
  -- Goal: `(γ.reverse).toPath ⟨s, hs⟩ = γ.toPath ⟨1 - s, _⟩`.
  -- `(γ.reverse).toPath = γ.toPath.symm` (definitionally from the
  -- `SmoothPath.reverse` constructor). And `γ.toPath.symm ⟨s, hs⟩
  --   = γ.toPath (unitInterval.symm ⟨s, hs⟩) = γ.toPath ⟨1-s, _⟩`.
  show (γ.toPath.symm) ⟨s, hs⟩ = γ.toPath ⟨1 - s, h_one_sub_unit⟩
  rfl

/-! ## Eventually-equal on `Ioo 0 1` -/

/-- **On `Ioo 0 1`, the reverse's ambient locally matches
`γ.ambient ∘ (1 - ·)`.** This is the bridge from the Classical.choose
witness to the explicit reverse formula, used in the velocity
identity. -/
lemma reverseAmbient_eventuallyEq (γ : SmoothPath I X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.reverse.ambient =ᶠ[𝓝 t] (fun s : ℝ => γ.ambient (1 - s)) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  have hs_unit : s ∈ unitInterval := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact γ.reverseAmbient_eq_on_unitInterval s hs_unit

/-! ## `mfderiv` of `1 - ·` -/

/-- **`mfderiv (1 - ·) t (1) = -1`.** Via `mfderiv_eq_fderiv` reduces
to a real-analysis fact: `fderiv ℝ (fun s ↦ 1 - s) t` applied to `1`
is `-1`. -/
lemma mfderiv_one_sub_apply_one (t : ℝ) :
    (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => 1 - s) t) (1 : ℝ)
      = (-1 : ℝ) := by
  -- Reduce mfderiv to fderiv.
  rw [mfderiv_eq_fderiv]
  -- Compute `fderiv ℝ (1 - ·) t = -id` via `HasFDerivAt`.
  have h_one : HasFDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ →L[ℝ] ℝ) t :=
    hasFDerivAt_const _ _
  have h_id : HasFDerivAt (fun s : ℝ => s) (ContinuousLinearMap.id ℝ ℝ) t :=
    hasFDerivAt_id t
  have h_diff : HasFDerivAt (fun s : ℝ => 1 - s)
      (0 - ContinuousLinearMap.id ℝ ℝ) t := h_one.sub h_id
  rw [h_diff.fderiv]
  show ((0 : ℝ →L[ℝ] ℝ) - ContinuousLinearMap.id ℝ ℝ) (1 : ℝ) = -1
  simp

/-! ## Velocity identity for the reverse path on `Ioo 0 1` -/

/-- **`MDifferentiableAt` of `1 - ·`.** Trivial via continuous-linear,
but stated for use in chain rule. -/
private lemma mdifferentiableAt_one_sub (t : ℝ) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun s : ℝ => 1 - s) t := by
  have h : Differentiable ℝ (fun s : ℝ => 1 - s) :=
    (differentiable_const (1 : ℝ)).sub differentiable_id
  exact (h.mdifferentiable.mdifferentiableAt :)

/-- **Velocity of the reversed path.** On the open interior
`Ioo 0 1`, `(γ.reverse).velocity t = -(γ.velocity (1 - t))`. -/
lemma velocity_reverse_of_mem_Ioo (γ : SmoothPath I X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.reverse.velocity t = -(γ.velocity (1 - t)) := by
  unfold velocity
  -- mfderiv of γ.reverse.ambient at t equals mfderiv of the explicit
  -- composition `γ.ambient ∘ (1 - ·)` at t, via the eventuallyEq.
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I γ.reverse.ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => γ.ambient (1 - s)) t :=
    (γ.reverseAmbient_eventuallyEq ht).mfderiv_eq
  rw [h_eq]
  -- Chain rule: `mfderiv (γ.ambient ∘ (1 - ·)) t 1
  --   = (mfderiv γ.ambient (1 - t)) ((mfderiv (1 - ·) t) 1)`.
  have h_amb_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) I γ.ambient (1 - t) :=
    (γ.ambient_contMDiff (1 - t)).mdifferentiableAt (by decide)
  have h_sub_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun s : ℝ => 1 - s) t :=
    mdifferentiableAt_one_sub t
  show mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => γ.ambient (1 - s)) t (1 : ℝ)
        = -(mfderiv (𝓘(ℝ, ℝ)) I γ.ambient (1 - t) (1 : ℝ))
  -- Recognize `fun s => γ.ambient (1 - s)` as `γ.ambient ∘ (1 - ·)`.
  change (mfderiv (𝓘(ℝ, ℝ)) I (γ.ambient ∘ (fun s : ℝ => 1 - s)) t) (1 : ℝ)
        = -(mfderiv (𝓘(ℝ, ℝ)) I γ.ambient (1 - t) (1 : ℝ))
  rw [mfderiv_comp_apply t h_amb_diff h_sub_diff]
  rw [mfderiv_one_sub_apply_one t]
  -- Goal: `(mfderiv γ.ambient (1 - t)) (-1) = -(mfderiv γ.ambient (1 - t)) 1`.
  have h_neg : (-1 : ℝ) = -(1 : ℝ) := rfl
  rw [h_neg]
  exact (mfderiv (𝓘(ℝ, ℝ)) I γ.ambient (1 - t)).map_neg (1 : ℝ)

/-! ## Integrand identity for the reverse path on `Ioo 0 1` -/

/-- **The reverse-integrand equals `-(integrand at 1-t)` on
`Ioo 0 1`.** Combines the ambient/velocity identities with
`applyCotangent` linearity. -/
lemma integrand_reverse_of_mem_Ioo (γ : SmoothPath I X)
    (om : SmoothOneForm I X) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.reverse.integrand om t = -(γ.integrand om (1 - t)) := by
  unfold integrand
  -- Use the ambient identity at `t ∈ unitInterval`.
  have ht_unit : t ∈ unitInterval := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  rw [γ.reverseAmbient_eq_on_unitInterval t ht_unit]
  -- Use the velocity identity.
  rw [γ.velocity_reverse_of_mem_Ioo ht]
  -- Now: applyCotangent (om (γ.ambient (1 - t))) (-(γ.velocity (1 - t)))
  --   = -(applyCotangent (om (γ.ambient (1 - t))) (γ.velocity (1 - t))).
  unfold applyCotangent
  rw [ContinuousLinearMap.map_neg]

/-! ## Integral identity -/

/-- **The reverse-path integral is the negative of the forward
integral.** `(γ.reverse).integrate ω = -(γ.integrate ω)`. -/
theorem integrate_reverse (γ : SmoothPath I X) (om : SmoothOneForm I X) :
    γ.reverse.integrate om = -(γ.integrate om) := by
  -- Step 1: rewrite the reverse integrand to `-(γ.integrand om (1 - ·))`
  -- almost everywhere on `Ι 0 1 = Ioc 0 1`. Singleton `{1}` is the
  -- only point where the rewrite may fail (the endpoint of `[0, 1]`,
  -- where `Ioo 0 1` excludes it); `{1}` has measure zero.
  have h_meas_one : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
    Real.volume_singleton
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact h_meas_one
  unfold integrate
  -- Show the reverse integrand equals `-(γ.integrand om (1 - ·))` a.e.
  -- on `Ι 0 1 = Ioc 0 1`, then apply `integral_congr_ae`.
  have h_congr : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
        γ.reverse.integrand om x = -(γ.integrand om (1 - x)) := by
    filter_upwards [h_almost] with x hx hx_uIoc
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_uIoc
    -- `hx_uIoc : x ∈ Ioc 0 1`. With `hx : x ≠ 1`, derive `x ∈ Ioo 0 1`.
    exact γ.integrand_reverse_of_mem_Ioo om
      ⟨hx_uIoc.1, lt_of_le_of_ne hx_uIoc.2 hx⟩
  rw [intervalIntegral.integral_congr_ae h_congr]
  -- Goal: `∫ t in 0..1, -(γ.integrand om (1 - t)) = -(∫ t in 0..1, γ.integrand om t)`.
  rw [intervalIntegral.integral_neg]
  congr 1
  -- Goal: `∫ t in 0..1, γ.integrand om (1 - t) = ∫ t in 0..1, γ.integrand om t`.
  -- Substitution `t ↦ 1 - t` on `[0, 1]` via `integral_comp_sub_left`:
  -- `∫ x in 0..1, f (1 - x) = ∫ x in (1-1)..(1-0), f x = ∫ x in 0..1, f x`.
  have h_sub : (∫ x in (0 : ℝ)..1, γ.integrand om (1 - x))
      = ∫ x in (1 - 1 : ℝ)..(1 - 0), γ.integrand om x :=
    intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
      (γ.integrand om) (1 : ℝ)
  simpa using h_sub

end SmoothPath

end
