/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexAffineSegmentPathReverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

/-! # Midpoint splitting for `affineSegmentPath` integrate

The `affineSegmentPath σ p q` integrates *additively* under midpoint
splitting: with `m = (a + c) / 2`,

```
(affineSegmentPath σ a c).integrate ω
  = (affineSegmentPath σ a m).integrate ω + (affineSegmentPath σ m c).integrate ω
```

Strategy. Reparameterise the left-half by `t ↦ t/2` and the right-half
by `t ↦ 1/2 + t/2`. The two half-paths' ambient extensions equal the
full path's ambient extension composed with the reparametrisation on a
neighborhood of any interior `t ∈ (0, 1)`, so velocities pick up the
factor `1/2` via the chain rule. The integrand identity

```
(affineSegmentPath σ a m).integrand ω t = (1/2) * (affineSegmentPath σ a c).integrand ω (t/2)
```

then holds on `(0, 1)`, whence on `[0, 1]` modulo measure zero. The
substitution `intervalIntegral.integral_comp_div` (with `c = 2`)
converts `∫_0^1 (1/2) * f(t/2) dt = ∫_0^{1/2} f t dt`. Symmetric
argument for the right half via `1/2 + t/2`. Adjacent-intervals
gluing closes the identity.

No `sorry`, no `axiom`. -/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace Smooth2Simplex

/-! ## The midpoint and basic reparameterisations -/

/-- **Midpoint** of `a c : Fin 2 → ℝ`. -/
def midpoint2 (a c : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => (a i + c i) / 2

/-- **`lineParam` and `midpoint2`**: `lineParam a (midpoint2 a c) t = lineParam a c (t/2)`. -/
lemma lineParam_left_half (a c : Fin 2 → ℝ) (t : ℝ) :
    lineParam a (midpoint2 a c) t = lineParam a c (t / 2) := by
  unfold lineParam midpoint2
  ext i
  show (1 - t) * a i + t * ((a i + c i) / 2) = (1 - t / 2) * a i + (t / 2) * c i
  ring

/-- **`lineParam` and `midpoint2`**: `lineParam (midpoint2 a c) c t = lineParam a c (1/2 + t/2)`. -/
lemma lineParam_right_half (a c : Fin 2 → ℝ) (t : ℝ) :
    lineParam (midpoint2 a c) c t = lineParam a c (1/2 + t/2) := by
  unfold lineParam midpoint2
  ext i
  show (1 - t) * ((a i + c i) / 2) + t * c i
        = (1 - (1/2 + t/2)) * a i + (1/2 + t/2) * c i
  ring

/-! ## Setting up the manifold-side velocity computation -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- **`affineSegmentPath σ p q` ambient agrees with `σ.toFun ∘ lineParam p q`
on `unitInterval`.** Direct application of `ambient_eq_on_unitInterval`,
since the underlying continuous path is `t ↦ σ.toFun (lineParam p q t.val)`. -/
lemma affineSegmentPath_ambient_on_unitInterval (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) {t : ℝ} (ht : t ∈ unitInterval) :
    (affineSegmentPath σ p q).ambient t = σ.toFun (lineParam p q t) := by
  have h := (affineSegmentPath σ p q).ambient_eq_on_unitInterval ⟨t, ht⟩
  have h_val : ((⟨t, ht⟩ : unitInterval).val : ℝ) = t := rfl
  rw [h_val] at h
  rw [h]
  -- `(affineSegmentPath σ p q).toPath ⟨t, ht⟩ = σ.toFun (lineParam p q t)` by the
  -- definition of the Path field.
  rfl

/-- **`affineSegmentPath σ p q` ambient equals `σ.toFun ∘ lineParam p q` on
`Ioo 0 1`.** Direct corollary. -/
lemma affineSegmentPath_ambient_on_Ioo (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ p q).ambient t = σ.toFun (lineParam p q t) :=
  affineSegmentPath_ambient_on_unitInterval σ p q
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩

/-- **`affineSegmentPath σ p q` ambient eventually-equals
`σ.toFun ∘ lineParam p q` near any `t ∈ Ioo 0 1`.** -/
lemma affineSegmentPath_ambient_eventuallyEq (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ p q).ambient =ᶠ[𝓝 t]
      (fun s : ℝ => σ.toFun (lineParam p q s)) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  exact affineSegmentPath_ambient_on_Ioo σ p q hs

/-! ## Velocity formula on the interior

The velocity of `affineSegmentPath σ p q` at `t ∈ (0, 1)` is
`mfderiv (σ ∘ lineParam p q) t (1)`, which by the chain rule equals
`mfderiv σ (lineParam p q t) ((mfderiv (lineParam p q) t)(1))`, i.e.,
`mfderiv σ (lineParam p q t) (q - p)`. -/

/-- **`mfderiv` of `lineParam p q` at `t` applied to `1` equals `q - p`.** -/
lemma mfderiv_lineParam_apply_one (p q : Fin 2 → ℝ) (t : ℝ) :
    (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) (lineParam p q) t) (1 : ℝ)
      = q - p := by
  rw [mfderiv_eq_fderiv]
  -- `fderiv` of `t ↦ (1 - t) • p + t • q` at `t` evaluated at `1`
  -- equals `-p + q = q - p`.
  have h_eq : (lineParam p q) = fun s : ℝ => -(s • p) + s • q + p := by
    funext s
    show (1 - s) • p + s • q = -(s • p) + s • q + p
    rw [sub_smul, one_smul]
    abel
  rw [h_eq]
  -- Now compute fderiv of `s ↦ -(s • p) + s • q + p`.
  have h1 : HasFDerivAt (fun s : ℝ => s • p)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) p) t :=
    (hasFDerivAt_id t).smul_const p
  have h2 : HasFDerivAt (fun s : ℝ => s • q)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) q) t :=
    (hasFDerivAt_id t).smul_const q
  have h3 : HasFDerivAt (fun s : ℝ => -(s • p))
      (-ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) p) t := h1.neg
  have h4 : HasFDerivAt (fun s : ℝ => -(s • p) + s • q)
      (-ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) p +
       ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) q) t := h3.add h2
  have h5 : HasFDerivAt (fun s : ℝ => -(s • p) + s • q + p)
      (-ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) p +
       ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) q) t := h4.add_const p
  rw [h5.fderiv]
  -- Apply to `1 : ℝ`.
  show (-ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) p
        + ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) q) (1 : ℝ)
      = q - p
  simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply]
  abel

/-- **MDifferentiableAt of `lineParam p q` at any `t`**. -/
lemma mdifferentiableAt_lineParam (p q : Fin 2 → ℝ) (t : ℝ) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, Fin 2 → ℝ)) (lineParam p q) t :=
  ((lineParam_contMDiff p q).contMDiffAt).mdifferentiableAt (by decide)

/-- **MDifferentiableAt of `σ.toFun` at any point in `Fin 2 → ℝ`**. -/
lemma mdifferentiableAt_smooth2Simplex (σ : Smooth2Simplex I X)
    (x : Fin 2 → ℝ) :
    MDifferentiableAt (𝓘(ℝ, Fin 2 → ℝ)) I σ.toFun x :=
  ((σ.smooth).contMDiffAt).mdifferentiableAt (by decide)

/-- **Velocity of `affineSegmentPath σ p q` at `t ∈ Ioo 0 1`** equals
`mfderiv σ.toFun (lineParam p q t) (q - p)`. -/
lemma affineSegmentPath_velocity_of_mem_Ioo
    (σ : Smooth2Simplex I X) (p q : Fin 2 → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ p q).velocity t
      = (mfderiv (𝓘(ℝ, Fin 2 → ℝ)) I σ.toFun (lineParam p q t)) (q - p) := by
  unfold SmoothPath.velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I (affineSegmentPath σ p q).ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I
          (fun s : ℝ => σ.toFun (lineParam p q s)) t :=
    (affineSegmentPath_ambient_eventuallyEq σ p q ht).mfderiv_eq
  rw [h_eq]
  -- Chain rule: σ.toFun ∘ lineParam.
  have h_lp := mdifferentiableAt_lineParam p q t
  have h_σ := mdifferentiableAt_smooth2Simplex σ (lineParam p q t)
  show (mfderiv (𝓘(ℝ, ℝ)) I (σ.toFun ∘ lineParam p q) t) (1 : ℝ)
      = (mfderiv (𝓘(ℝ, Fin 2 → ℝ)) I σ.toFun (lineParam p q t)) (q - p)
  rw [mfderiv_comp_apply t h_σ h_lp, mfderiv_lineParam_apply_one]

/-! ## Velocity scaling under midpoint subdivision -/

/-- **Velocity of left-half affineSegmentPath at `t ∈ Ioo 0 1`** equals
`(1/2) • velocity of full affineSegmentPath at `(t/2)`.

`(affineSegmentPath σ a (midpoint2 a c)).velocity t
  = (1/2) • (affineSegmentPath σ a c).velocity (t/2)`. -/
lemma affineSegmentPath_velocity_left_half
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ a (midpoint2 a c)).velocity t
      = (1 / 2 : ℝ) • (affineSegmentPath σ a c).velocity (t / 2) := by
  have ht_half : t / 2 ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [affineSegmentPath_velocity_of_mem_Ioo σ a (midpoint2 a c) ht,
      affineSegmentPath_velocity_of_mem_Ioo σ a c ht_half,
      lineParam_left_half]
  -- Goal: mfderiv σ (lineParam a c (t/2)) (midpoint2 a c - a)
  --     = (1/2) • mfderiv σ (lineParam a c (t/2)) (c - a)
  have h_diff : midpoint2 a c - a = (1 / 2 : ℝ) • (c - a) := by
    unfold midpoint2
    funext i
    show (a i + c i) / 2 - a i = (1 / 2 : ℝ) * (c i - a i)
    ring
  rw [h_diff]
  exact (mfderiv (𝓘(ℝ, Fin 2 → ℝ)) I σ.toFun (lineParam a c (t / 2))).map_smul
    (1 / 2 : ℝ) (c - a)

/-- **Velocity of right-half affineSegmentPath at `t ∈ Ioo 0 1`** equals
`(1/2) • velocity of full affineSegmentPath at `(1/2 + t/2)`. -/
lemma affineSegmentPath_velocity_right_half
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ (midpoint2 a c) c).velocity t
      = (1 / 2 : ℝ) • (affineSegmentPath σ a c).velocity (1/2 + t/2) := by
  have ht_shift : 1/2 + t/2 ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [affineSegmentPath_velocity_of_mem_Ioo σ (midpoint2 a c) c ht,
      affineSegmentPath_velocity_of_mem_Ioo σ a c ht_shift,
      lineParam_right_half]
  have h_diff : c - midpoint2 a c = (1 / 2 : ℝ) • (c - a) := by
    unfold midpoint2
    funext i
    show c i - (a i + c i) / 2 = (1 / 2 : ℝ) * (c i - a i)
    ring
  rw [h_diff]
  exact (mfderiv (𝓘(ℝ, Fin 2 → ℝ)) I σ.toFun (lineParam a c (1/2 + t / 2))).map_smul
    (1 / 2 : ℝ) (c - a)

/-! ## Integrand scaling identities

`(affineSegmentPath σ a (midpoint2 a c)).integrand om t
  = (1/2) * (affineSegmentPath σ a c).integrand om (t/2)`. -/

/-- **Integrand of left-half affineSegmentPath at `t ∈ Ioo 0 1`.** -/
lemma affineSegmentPath_integrand_left_half
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ) (om : SmoothOneForm I X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ a (midpoint2 a c)).integrand om t
      = (1 / 2 : ℝ) * (affineSegmentPath σ a c).integrand om (t / 2) := by
  have ht_half : t / 2 ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold SmoothPath.integrand
  rw [affineSegmentPath_ambient_on_Ioo σ a (midpoint2 a c) ht,
      affineSegmentPath_ambient_on_Ioo σ a c ht_half,
      lineParam_left_half]
  -- Goal: applyCotangent (om (σ(lineParam a c (t/2))))
  --         ((affineSegmentPath σ a (midpoint2 a c)).velocity t)
  --       = (1/2) * applyCotangent (om (σ(lineParam a c (t/2))))
  --         ((affineSegmentPath σ a c).velocity (t/2))
  rw [affineSegmentPath_velocity_left_half σ a c ht]
  -- LHS now: applyCotangent (om (...)) ((1/2) • velocity_full(t/2)).
  -- Use linearity in the second arg: applyCotangent φ (c • v) = c * applyCotangent φ v.
  unfold SmoothPath.applyCotangent
  rw [ContinuousLinearMap.map_smul]
  rfl

/-- **Integrand of right-half affineSegmentPath at `t ∈ Ioo 0 1`.** -/
lemma affineSegmentPath_integrand_right_half
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ) (om : SmoothOneForm I X)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (affineSegmentPath σ (midpoint2 a c) c).integrand om t
      = (1 / 2 : ℝ) * (affineSegmentPath σ a c).integrand om (1/2 + t/2) := by
  have ht_shift : 1/2 + t/2 ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by linarith [ht.1], by linarith [ht.2]⟩
  unfold SmoothPath.integrand
  rw [affineSegmentPath_ambient_on_Ioo σ (midpoint2 a c) c ht,
      affineSegmentPath_ambient_on_Ioo σ a c ht_shift,
      lineParam_right_half]
  rw [affineSegmentPath_velocity_right_half σ a c ht]
  unfold SmoothPath.applyCotangent
  rw [ContinuousLinearMap.map_smul]
  rfl

/-! ## Continuity of integrands (for ae-rewriting and substitution) -/

lemma affineSegmentPath_continuous_integrand (σ : Smooth2Simplex I X)
    (p q : Fin 2 → ℝ) (om : SmoothOneForm I X) :
    Continuous ((affineSegmentPath σ p q).integrand om) :=
  (affineSegmentPath σ p q).continuous_integrand om

/-! ## Integrate identities for the two halves -/

/-- **Left-half integrate equals the full-path integral on `[0, 1/2]`.**

`(affineSegmentPath σ a (midpoint2 a c)).integrate om
  = ∫_0^{1/2} (affineSegmentPath σ a c).integrand om u du`. -/
theorem affineSegmentPath_integrate_left_half
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ) (om : SmoothOneForm I X) :
    (affineSegmentPath σ a (midpoint2 a c)).integrate om
      = ∫ u in (0 : ℝ)..(1/2 : ℝ),
          (affineSegmentPath σ a c).integrand om u := by
  unfold SmoothPath.integrate
  -- Goal: ∫_0^1 (left).integrand om t dt = ∫_0^{1/2} (full).integrand om u du.
  -- Step 1: rewrite (left).integrand a.e. on Ι 0 1 using
  --   (left).integrand t = (1/2) * (full).integrand (t/2) (on Ioo 0 1).
  have h_meas_endpoints : MeasureTheory.volume ({0, 1} : Set ℝ) = 0 := by
    rw [show ({0, 1} : Set ℝ) = {0} ∪ {1} from rfl]
    rw [MeasureTheory.measure_union_null Real.volume_singleton
          Real.volume_singleton]
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (0 : ℝ) ∧ x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨({0, 1} : Set ℝ)ᶜ, ?_, ?_⟩
    · rw [MeasureTheory.mem_ae_iff, compl_compl]; exact h_meas_endpoints
    · intro x hx
      refine ⟨?_, ?_⟩
      · intro h; exact hx (by simp [h])
      · intro h; exact hx (by simp [h])
  have h_congr : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (0 : ℝ) 1 →
        (affineSegmentPath σ a (midpoint2 a c)).integrand om t
          = (1 / 2 : ℝ) *
            (affineSegmentPath σ a c).integrand om (t / 2) := by
    filter_upwards [h_almost] with t ⟨ht0, ht1⟩ ht_uIoc
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_uIoc
    have ht_Ioo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨ht_uIoc.1, lt_of_le_of_ne ht_uIoc.2 ht1⟩
    exact affineSegmentPath_integrand_left_half σ a c om ht_Ioo
  rw [intervalIntegral.integral_congr_ae h_congr]
  -- Goal: ∫_0^1 (1/2) * (full).integrand om (t/2) dt = ∫_0^{1/2} ... du.
  -- Pull out (1/2) via integral_const_mul.
  rw [intervalIntegral.integral_const_mul]
  -- Goal: (1/2) * ∫_0^1 (full).integrand om (t/2) dt = ∫_0^{1/2} ... du.
  -- Apply integral_comp_div with c = 2.
  rw [intervalIntegral.integral_comp_div (fun u => (affineSegmentPath σ a c).integrand om u)
        (by norm_num : (2 : ℝ) ≠ 0)]
  -- Goal: (1/2) * (2 • ∫_{0/2}^{1/2} ... du) = ∫_0^{1/2} ... du.
  simp [smul_eq_mul]

/-- **Right-half integrate equals the full-path integral on `[1/2, 1]`.**

`(affineSegmentPath σ (midpoint2 a c) c).integrate om
  = ∫_{1/2}^1 (affineSegmentPath σ a c).integrand om u du`. -/
theorem affineSegmentPath_integrate_right_half
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ) (om : SmoothOneForm I X) :
    (affineSegmentPath σ (midpoint2 a c) c).integrate om
      = ∫ u in (1/2 : ℝ)..(1 : ℝ),
          (affineSegmentPath σ a c).integrand om u := by
  unfold SmoothPath.integrate
  have h_meas_endpoints : MeasureTheory.volume ({0, 1} : Set ℝ) = 0 := by
    rw [show ({0, 1} : Set ℝ) = {0} ∪ {1} from rfl]
    rw [MeasureTheory.measure_union_null Real.volume_singleton
          Real.volume_singleton]
  have h_almost : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (0 : ℝ) ∧ x ≠ (1 : ℝ) := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨({0, 1} : Set ℝ)ᶜ, ?_, ?_⟩
    · rw [MeasureTheory.mem_ae_iff, compl_compl]; exact h_meas_endpoints
    · intro x hx
      refine ⟨?_, ?_⟩
      · intro h; exact hx (by simp [h])
      · intro h; exact hx (by simp [h])
  have h_congr : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (0 : ℝ) 1 →
        (affineSegmentPath σ (midpoint2 a c) c).integrand om t
          = (1 / 2 : ℝ) *
            (affineSegmentPath σ a c).integrand om (1/2 + t / 2) := by
    filter_upwards [h_almost] with t ⟨ht0, ht1⟩ ht_uIoc
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_uIoc
    have ht_Ioo : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨ht_uIoc.1, lt_of_le_of_ne ht_uIoc.2 ht1⟩
    exact affineSegmentPath_integrand_right_half σ a c om ht_Ioo
  rw [intervalIntegral.integral_congr_ae h_congr]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_add_div
        (fun u => (affineSegmentPath σ a c).integrand om u)
        (by norm_num : (2 : ℝ) ≠ 0) (1/2 : ℝ)]
  simp [smul_eq_mul]
  norm_num

/-! ## Midpoint splitting: the full integrate identity -/

/-- **Midpoint splitting for `affineSegmentPath` integrate.**

For any `σ : Smooth2Simplex I X`, any `a c : Fin 2 → ℝ`, and any
smooth 1-form `om`:

```
(affineSegmentPath σ a c).integrate om
  = (affineSegmentPath σ a (midpoint2 a c)).integrate om
    + (affineSegmentPath σ (midpoint2 a c) c).integrate om
```

The proof composes the two half-identities with
`intervalIntegral.integral_add_adjacent_intervals` at `t = 1/2`. -/
theorem affineSegmentPath_integrate_midpoint_split
    (σ : Smooth2Simplex I X) (a c : Fin 2 → ℝ) (om : SmoothOneForm I X) :
    (affineSegmentPath σ a c).integrate om
      = (affineSegmentPath σ a (midpoint2 a c)).integrate om
        + (affineSegmentPath σ (midpoint2 a c) c).integrate om := by
  rw [affineSegmentPath_integrate_left_half,
      affineSegmentPath_integrate_right_half]
  unfold SmoothPath.integrate
  have h_cont : Continuous ((affineSegmentPath σ a c).integrand om) :=
    (affineSegmentPath σ a c).continuous_integrand om
  exact (intervalIntegral.integral_add_adjacent_intervals
    (h_cont.intervalIntegrable 0 (1/2))
    (h_cont.intervalIntegrable (1/2) 1)).symm

end Smooth2Simplex

end JacobianChallenge

end
