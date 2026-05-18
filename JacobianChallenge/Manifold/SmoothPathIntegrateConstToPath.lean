/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathIntegrateConst
import JacobianChallenge.Manifold.Smooth2SimplexConst

set_option linter.unusedSectionVars false

/-! # `SmoothPath.integrate` vanishes for any path with constant `toPath`

`SmoothPathIntegrateConst.lean` proves `(SmoothPath.const I X P).integrate ω = 0`
for the canonical constant `SmoothPath`. This file generalises that
result to **any** `γ : SmoothPath I X` whose underlying continuous
path `γ.toPath` is pointwise constant at some `P : X`.

The generalisation matters for the constant 2-simplex chip: the
three faces `face0/1/2 (Smooth2Simplex.const P)` are *not*
syntactically equal to `SmoothPath.const I X P` (the latter uses
`Path.refl P` directly while the faces use the structurally-different
`pathOfUnitIntervalMap` helper), but they all have the same underlying
toPath, namely `fun _ : unitInterval => P`. Hence each face integrates
to zero against any smooth 1-form.

## What this file ships

* `SmoothPath.integrate_eq_zero_of_toPath_eq_const` — the generic
  lemma.
* `Smooth2Simplex.face0_const_integrate_eq_zero` /
  `face1_const_integrate_eq_zero` / `face2_const_integrate_eq_zero` —
  applied to the constant 2-simplex faces.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter Topology JacobianChallenge
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-- **Ambient equals `P` on the unit interval, given constant `toPath`.**
A direct consequence of `ambient_eq_on_unitInterval`: any ambient
witness `f` of a smooth-path-with-constant-toPath satisfies `f s = P`
for `s ∈ unitInterval`. -/
lemma ambient_eq_of_mem_unitInterval_of_toPath_const
    (γ : SmoothPath I X) {P : X}
    (h_const : ∀ s : unitInterval, γ.toPath s = P)
    (s : ℝ) (hs : s ∈ unitInterval) :
    γ.ambient s = P := by
  have h_eq := γ.ambient_eq_on_unitInterval ⟨s, hs⟩
  have h_val : (⟨s, hs⟩ : unitInterval).val = s := rfl
  rw [h_val] at h_eq
  rw [h_eq]
  exact h_const ⟨s, hs⟩

/-- **Ambient is constantly `P` near every interior point.** -/
lemma ambient_eventuallyEq_const_of_toPath_const
    (γ : SmoothPath I X) {P : X}
    (h_const : ∀ s : unitInterval, γ.toPath s = P)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.ambient =ᶠ[𝓝 t] (fun _ : ℝ => P) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  have hs_unit : s ∈ unitInterval :=
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact ambient_eq_of_mem_unitInterval_of_toPath_const γ h_const s hs_unit

/-- **Velocity vanishes on `(0, 1)`.** -/
lemma velocity_of_mem_Ioo_of_toPath_const
    (γ : SmoothPath I X) {P : X}
    (h_const : ∀ s : unitInterval, γ.toPath s = P)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.velocity t = 0 := by
  unfold velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I γ.ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I (fun _ : ℝ => P) t :=
    (ambient_eventuallyEq_const_of_toPath_const γ h_const ht).mfderiv_eq
  rw [h_eq]
  have h_const' : mfderiv (𝓘(ℝ, ℝ)) I (fun _ : ℝ => P) t
      = (0 : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
            TangentSpace I ((fun _ : ℝ => P) t)) :=
    mfderiv_const
  rw [h_const']
  show ((0 : ℝ →L[ℝ] TangentSpace I ((fun _ : ℝ => P) t)) (1 : ℝ)) = 0
  exact ContinuousLinearMap.zero_apply (1 : ℝ)

/-- **Integrand vanishes on `(0, 1)`.** -/
lemma integrand_of_mem_Ioo_of_toPath_const
    (γ : SmoothPath I X) {P : X}
    (h_const : ∀ s : unitInterval, γ.toPath s = P)
    (ω : SmoothOneForm I X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.integrand ω t = 0 := by
  unfold integrand
  rw [velocity_of_mem_Ioo_of_toPath_const γ h_const ht]
  unfold applyCotangent
  exact ContinuousLinearMap.map_zero _

/-- **Generic constant-toPath integrate-vanishing lemma.** Any smooth
path `γ` whose underlying continuous path is pointwise constant
integrates to zero against any smooth 1-form. -/
theorem integrate_eq_zero_of_toPath_eq_const
    (γ : SmoothPath I X) {P : X}
    (h_const : ∀ s : unitInterval, γ.toPath s = P)
    (ω : SmoothOneForm I X) :
    γ.integrate ω = 0 := by
  unfold integrate
  refine intervalIntegral.integral_zero_ae ?_
  have h_meas_zero : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
    Real.volume_singleton
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
    rw [MeasureTheory.mem_ae_iff, compl_compl]
    exact h_meas_zero
  filter_upwards [h_almost] with x hx hx_Ι
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx_Ι
  exact integrand_of_mem_Ioo_of_toPath_const γ h_const ω
    ⟨hx_Ι.1, lt_of_le_of_ne hx_Ι.2 hx⟩

end SmoothPath

/-! ## Application: constant 2-simplex faces -/

namespace JacobianChallenge

/-- The `toPath` of `face0 (const P)` is pointwise constant at `P`. -/
lemma face0_const_toPath_eq_const (P : X) :
    ∀ s : unitInterval,
      (Smooth2Simplex.face0 (Smooth2Simplex.const I X P)).toPath s = P := by
  intro s
  -- Unfold face0 of const: toPath at s is
  -- `(const P).toFun (face0Param s.val) = P`.
  rfl

/-- The `toPath` of `face1 (const P)` is pointwise constant at `P`. -/
lemma face1_const_toPath_eq_const (P : X) :
    ∀ s : unitInterval,
      (Smooth2Simplex.face1 (Smooth2Simplex.const I X P)).toPath s = P := by
  intro s
  rfl

/-- The `toPath` of `face2 (const P)` is pointwise constant at `P`. -/
lemma face2_const_toPath_eq_const (P : X) :
    ∀ s : unitInterval,
      (Smooth2Simplex.face2 (Smooth2Simplex.const I X P)).toPath s = P := by
  intro s
  rfl

/-- **`face0 (const P)` integrates to zero against any smooth
1-form.** -/
theorem face0_const_integrate_eq_zero (P : X) (ω : SmoothOneForm I X) :
    (Smooth2Simplex.face0 (Smooth2Simplex.const I X P)).integrate ω = 0 :=
  SmoothPath.integrate_eq_zero_of_toPath_eq_const _
    (face0_const_toPath_eq_const P) ω

/-- **`face1 (const P)` integrates to zero against any smooth
1-form.** -/
theorem face1_const_integrate_eq_zero (P : X) (ω : SmoothOneForm I X) :
    (Smooth2Simplex.face1 (Smooth2Simplex.const I X P)).integrate ω = 0 :=
  SmoothPath.integrate_eq_zero_of_toPath_eq_const _
    (face1_const_toPath_eq_const P) ω

/-- **`face2 (const P)` integrates to zero against any smooth
1-form.** -/
theorem face2_const_integrate_eq_zero (P : X) (ω : SmoothOneForm I X) :
    (Smooth2Simplex.face2 (Smooth2Simplex.const I X P)).integrate ω = 0 :=
  SmoothPath.integrate_eq_zero_of_toPath_eq_const _
    (face2_const_toPath_eq_const P) ω

end JacobianChallenge

end
