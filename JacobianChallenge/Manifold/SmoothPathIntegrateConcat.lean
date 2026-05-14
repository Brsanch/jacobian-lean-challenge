/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import JacobianChallenge.Manifold.SmoothPathConcat
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothPathIntegrability

set_option linter.unusedSectionVars false

/-! # `(γ.concat δ h).integrate = γ.integrate + δ.integrate`

The path-integral additivity identity under `SmoothPath.concat`:

    `(γ.concat δ h).integrate ω = γ.integrate ω + δ.integrate ω`.

## Strategy

On `Ioo 0 (1/2)`, the concat's ambient locally equals
`γ.ambient ∘ concatRepLeft`; the velocity is `concatRepLeft' t •
γ.velocity (concatRepLeft t)`; the integrand is `concatRepLeft' t •
γ.integrand ω (concatRepLeft t)`.

Apply `intervalIntegral.integral_deriv_smul_comp` (substitution
`u = concatRepLeft t`, with `concatRepLeft 0 = 0` and
`concatRepLeft (1/2) = 1`) to evaluate the integral on `[0, 1/2]`
as `γ.integrate ω`. The integral on `[1/2, 1]` is `δ.integrate ω`
by the symmetric argument with `concatRepRight`. Then
`intervalIntegral.integral_add_adjacent_intervals` glues.

No `sorry`, no `axiom`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

/-! ## Local-form ambient identities for concat -/

/-- **Concat ambient agrees with `γ.ambient ∘ concatRepLeft` on `[0, 1/2]`.**
The Classical-chosen ambient `(γ.concat δ h).ambient` and the
explicit `concatAmbient γ δ` (which equals `γ.ambient (concatRepLeft t)`
on `t ≤ 1/2`) both project to the same continuous path on
`unitInterval`, so they agree there. -/
lemma concat_ambient_eq_left_half (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1/2)) :
    (γ.concat δ h).ambient t = γ.ambient (concatRepLeft t) := by
  -- `t ∈ Icc 0 (1/2) ⊆ unitInterval`. Use `ambient_eq_on_unitInterval`
  -- on both sides to reduce to `toPath` equality, then apply the
  -- definition of `concat` to evaluate.
  have ht_unit : t ∈ unitInterval :=
    ⟨ht.1, by linarith [ht.2]⟩
  have h_concat := (γ.concat δ h).ambient_eq_on_unitInterval ⟨t, ht_unit⟩
  have h_concat_val : (⟨t, ht_unit⟩ : unitInterval).val = t := rfl
  rw [h_concat_val] at h_concat
  -- `h_concat : (concat).ambient t = (concat).toPath ⟨t, ht_unit⟩`.
  -- `(concat).toPath ⟨t, _⟩ = concatAmbient γ δ t = γ.ambient (concatRepLeft t)`
  -- when `t ≤ 1/2`.
  rw [h_concat]
  show (γ.concat δ h).toPath ⟨t, ht_unit⟩ = γ.ambient (concatRepLeft t)
  -- The underlying continuous path of `γ.concat δ h` is
  -- `fun s : unitInterval => γ.concatAmbient δ s.val`.
  show γ.concatAmbient δ t = γ.ambient (concatRepLeft t)
  show (if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                     else δ.ambient (concatRepRight t))
        = γ.ambient (concatRepLeft t)
  rw [if_pos ht.2]

/-- **Concat ambient agrees with `δ.ambient ∘ concatRepRight` on `[1/2, 1]`.**
For `t = 1/2`, both sides equal the junction point
`γ.tgt = δ.src` (under `h`). -/
lemma concat_ambient_eq_right_half (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) {t : ℝ}
    (ht : t ∈ Icc (1/2 : ℝ) 1) :
    (γ.concat δ h).ambient t = δ.ambient (concatRepRight t) := by
  have ht_unit : t ∈ unitInterval :=
    ⟨by linarith [ht.1], ht.2⟩
  have h_concat := (γ.concat δ h).ambient_eq_on_unitInterval ⟨t, ht_unit⟩
  have h_concat_val : (⟨t, ht_unit⟩ : unitInterval).val = t := rfl
  rw [h_concat_val] at h_concat
  rw [h_concat]
  show (γ.concat δ h).toPath ⟨t, ht_unit⟩ = δ.ambient (concatRepRight t)
  show γ.concatAmbient δ t = δ.ambient (concatRepRight t)
  show (if t ≤ 1/2 then γ.ambient (concatRepLeft t)
                     else δ.ambient (concatRepRight t))
        = δ.ambient (concatRepRight t)
  -- Case split on whether `t ≤ 1/2` (only `t = 1/2` is the boundary).
  by_cases ht_half : t ≤ 1/2
  · -- `t = 1/2` exactly (since `t ≥ 1/2` from `ht.1`).
    have ht_eq : t = 1/2 := le_antisymm ht_half ht.1
    subst ht_eq
    rw [if_pos (le_refl (1/2 : ℝ))]
    -- Goal: `γ.ambient (concatRepLeft (1/2)) = δ.ambient (concatRepRight (1/2))`.
    -- `concatRepLeft (1/2) = 1` (since `1/2 ≥ 3/8`).
    -- `concatRepRight (1/2) = 0` (since `1/2 ≤ 5/8`).
    rw [concatRepLeft_eq_one_of_ge (1/2) (by norm_num),
        concatRepRight_eq_zero_of_le (1/2) (by norm_num)]
    -- Goal: `γ.ambient 1 = δ.ambient 0`. By the unit-interval projections:
    -- `γ.ambient 1 = γ.toPath ⟨1, _⟩ = γ.tgt`, `δ.ambient 0 = δ.src`.
    -- Use `h : γ.tgt = δ.src`.
    have hγ : γ.ambient 1 = γ.tgt := by
      have := γ.ambient_eq_on_unitInterval
        ⟨1, by constructor <;> norm_num⟩
      have h1 : ((⟨1, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
          = 1 := rfl
      rw [h1] at this
      rw [this]
      exact γ.toPath.target'
    have hδ : δ.ambient 0 = δ.src := by
      have := δ.ambient_eq_on_unitInterval
        ⟨0, by constructor <;> norm_num⟩
      have h0 : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ)
          = 0 := rfl
      rw [h0] at this
      rw [this]
      exact δ.toPath.source'
    rw [hγ, hδ, h]
  · rw [if_neg ht_half]

/-! ## Local-form integrand identities for concat

The integrand identity `(γ.concat δ h).integrand ω t = ...` follows
from the ambient identity plus the chain rule for `velocity`. We
compute the velocity at `t ∈ Ioo 0 (1/2)` (resp `Ioo (1/2) 1`) via
`Filter.EventuallyEq.mfderiv_eq` and `mfderiv_comp_apply`. -/

private lemma concat_ambient_eventuallyEq_left (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1/2)) :
    (γ.concat δ h).ambient =ᶠ[𝓝 t]
      (fun s : ℝ => γ.ambient (concatRepLeft s)) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  -- `hs : s ∈ Ioo 0 (1/2)`, so `s ∈ Icc 0 (1/2)`.
  exact concat_ambient_eq_left_half γ δ h ⟨le_of_lt hs.1, le_of_lt hs.2⟩

private lemma concat_ambient_eventuallyEq_right (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) {t : ℝ}
    (ht : t ∈ Ioo (1/2 : ℝ) 1) :
    (γ.concat δ h).ambient =ᶠ[𝓝 t]
      (fun s : ℝ => δ.ambient (concatRepRight s)) := by
  refine eventually_of_mem (IsOpen.mem_nhds isOpen_Ioo ht) ?_
  intro s hs
  exact concat_ambient_eq_right_half γ δ h ⟨le_of_lt hs.1, le_of_lt hs.2⟩

/-! ## `mfderiv` reductions for concatRepLeft / concatRepRight -/

lemma mfderiv_concatRepLeft_apply_one (t : ℝ) :
    (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) concatRepLeft t) (1 : ℝ)
      = deriv concatRepLeft t := by
  rw [mfderiv_eq_fderiv]
  rfl

lemma mfderiv_concatRepRight_apply_one (t : ℝ) :
    (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) concatRepRight t) (1 : ℝ)
      = deriv concatRepRight t := by
  rw [mfderiv_eq_fderiv]
  rfl

/-! ## MDifferentiableAt of the reparameterisations -/

private lemma mdifferentiableAt_concatRepLeft (t : ℝ) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) concatRepLeft t := by
  rw [mdifferentiableAt_iff_differentiableAt]
  exact (contDiff_concatRepLeft.differentiable (by decide)).differentiableAt

private lemma mdifferentiableAt_concatRepRight (t : ℝ) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) concatRepRight t := by
  rw [mdifferentiableAt_iff_differentiableAt]
  exact (contDiff_concatRepRight.differentiable (by decide)).differentiableAt

/-! ## Velocity identities -/

/-- **Velocity on `Ioo 0 (1/2)`.** -/
lemma velocity_concat_of_mem_Ioo_left (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (1/2)) :
    (γ.concat δ h).velocity t
      = deriv concatRepLeft t • γ.velocity (concatRepLeft t) := by
  unfold velocity
  -- Eventually-equal reduces mfderiv to mfderiv of γ.ambient ∘ concatRepLeft.
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I (γ.concat δ h).ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I
          (fun s : ℝ => γ.ambient (concatRepLeft s)) t :=
    (concat_ambient_eventuallyEq_left γ δ h ht).mfderiv_eq
  rw [h_eq]
  -- Chain rule.
  have h_amb_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) I γ.ambient
      (concatRepLeft t) :=
    (γ.ambient_contMDiff (concatRepLeft t)).mdifferentiableAt (by decide)
  have h_rep_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) concatRepLeft t :=
    mdifferentiableAt_concatRepLeft t
  show (mfderiv (𝓘(ℝ, ℝ)) I (γ.ambient ∘ concatRepLeft) t) (1 : ℝ)
      = deriv concatRepLeft t • γ.velocity (concatRepLeft t)
  rw [mfderiv_comp_apply t h_amb_diff h_rep_diff,
      mfderiv_concatRepLeft_apply_one t]
  -- Goal: `(mfderiv γ.ambient (concatRepLeft t)) (deriv concatRepLeft t)
  --   = deriv concatRepLeft t • γ.velocity (concatRepLeft t)`.
  -- `mfderiv γ.ambient (concatRepLeft t)` is `ℝ-linear`: applying to a
  -- scalar `c : ℝ` equals `c • (applied to 1)`.
  conv_lhs => rw [show (deriv concatRepLeft t : ℝ)
                    = deriv concatRepLeft t • (1 : ℝ) by
                  rw [smul_eq_mul, mul_one]]
  exact (mfderiv (𝓘(ℝ, ℝ)) I γ.ambient (concatRepLeft t)).map_smul
    (deriv concatRepLeft t) (1 : ℝ)

/-- **Velocity on `Ioo (1/2) 1`.** -/
lemma velocity_concat_of_mem_Ioo_right (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) {t : ℝ} (ht : t ∈ Ioo (1/2 : ℝ) 1) :
    (γ.concat δ h).velocity t
      = deriv concatRepRight t • δ.velocity (concatRepRight t) := by
  unfold velocity
  have h_eq : mfderiv (𝓘(ℝ, ℝ)) I (γ.concat δ h).ambient t
      = mfderiv (𝓘(ℝ, ℝ)) I
          (fun s : ℝ => δ.ambient (concatRepRight s)) t :=
    (concat_ambient_eventuallyEq_right γ δ h ht).mfderiv_eq
  rw [h_eq]
  have h_amb_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) I δ.ambient
      (concatRepRight t) :=
    (δ.ambient_contMDiff (concatRepRight t)).mdifferentiableAt (by decide)
  have h_rep_diff : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) concatRepRight t :=
    mdifferentiableAt_concatRepRight t
  show (mfderiv (𝓘(ℝ, ℝ)) I (δ.ambient ∘ concatRepRight) t) (1 : ℝ)
      = deriv concatRepRight t • δ.velocity (concatRepRight t)
  rw [mfderiv_comp_apply t h_amb_diff h_rep_diff,
      mfderiv_concatRepRight_apply_one t]
  conv_lhs => rw [show (deriv concatRepRight t : ℝ)
                    = deriv concatRepRight t • (1 : ℝ) by
                  rw [smul_eq_mul, mul_one]]
  exact (mfderiv (𝓘(ℝ, ℝ)) I δ.ambient (concatRepRight t)).map_smul
    (deriv concatRepRight t) (1 : ℝ)

/-! ## Integrand identities -/

/-- **Integrand on `Ioo 0 (1/2)`.** -/
lemma integrand_concat_of_mem_Ioo_left (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) (om : SmoothOneForm I X) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1/2)) :
    (γ.concat δ h).integrand om t
      = deriv concatRepLeft t • γ.integrand om (concatRepLeft t) := by
  unfold integrand
  rw [concat_ambient_eq_left_half γ δ h ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
  rw [velocity_concat_of_mem_Ioo_left γ δ h ht]
  unfold applyCotangent
  rw [ContinuousLinearMap.map_smul]

/-- **Integrand on `Ioo (1/2) 1`.** -/
lemma integrand_concat_of_mem_Ioo_right (γ δ : SmoothPath I X)
    (h : γ.tgt = δ.src) (om : SmoothOneForm I X) {t : ℝ}
    (ht : t ∈ Ioo (1/2 : ℝ) 1) :
    (γ.concat δ h).integrand om t
      = deriv concatRepRight t • δ.integrand om (concatRepRight t) := by
  unfold integrand
  rw [concat_ambient_eq_right_half γ δ h ⟨le_of_lt ht.1, le_of_lt ht.2⟩]
  rw [velocity_concat_of_mem_Ioo_right γ δ h ht]
  unfold applyCotangent
  rw [ContinuousLinearMap.map_smul]

/-! ## Endpoint identities (helpers) -/

private lemma concatRepLeft_half : concatRepLeft (1/2 : ℝ) = 1 :=
  concatRepLeft_eq_one_of_ge (1/2) (by norm_num)

private lemma concatRepRight_half : concatRepRight (1/2 : ℝ) = 0 :=
  concatRepRight_eq_zero_of_le (1/2) (by norm_num)

/-! ## The integral identity -/

/-- **`(γ.concat δ h).integrate ω = γ.integrate ω + δ.integrate ω`.**

Split `[0, 1] = [0, 1/2] ∪ [1/2, 1]` via
`intervalIntegral.integral_add_adjacent_intervals`. On each half,
rewrite the integrand using the local-form identity
(`integrand_concat_of_mem_Ioo_left` / `_right`) modulo a null
singleton (the half's endpoint). Apply the substitution rule
`intervalIntegral.integral_deriv_smul_comp` with
`f = concatRepLeft` (resp `concatRepRight`); the endpoints map
`0 ↦ 0`, `1/2 ↦ 1` (resp `1/2 ↦ 0`, `1 ↦ 1`), recovering
`γ.integrate ω` and `δ.integrate ω` exactly. -/
theorem integrate_concat (γ δ : SmoothPath I X) (h : γ.tgt = δ.src)
    (om : SmoothOneForm I X) :
    (γ.concat δ h).integrate om = γ.integrate om + δ.integrate om := by
  -- Set up integrability witnesses.
  have h_cont_concat : Continuous ((γ.concat δ h).integrand om) :=
    (γ.concat δ h).continuous_integrand om
  -- Split the integral [0, 1] at 1/2.
  have h_split : (γ.concat δ h).integrate om
      = (∫ t in (0 : ℝ)..(1/2), (γ.concat δ h).integrand om t)
        + (∫ t in (1/2 : ℝ)..1, (γ.concat δ h).integrand om t) := by
    unfold integrate
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (h_cont_concat.intervalIntegrable 0 (1/2))
      (h_cont_concat.intervalIntegrable (1/2) 1)]
  rw [h_split]
  congr 1
  · -- Left half: `∫ t in 0..1/2, (concat).integrand om t = γ.integrate om`.
    -- Step 1: rewrite the integrand a.e. on `Ι 0 (1/2)` using the local form.
    have h_meas_half : MeasureTheory.volume ({1/2} : Set ℝ) = 0 :=
      Real.volume_singleton
    have h_almost_half : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1/2 : ℝ) := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{1/2}ᶜ, ?_, fun x hx => hx⟩
      rw [MeasureTheory.mem_ae_iff, compl_compl]
      exact h_meas_half
    have h_congr_left : ∀ᵐ x ∂MeasureTheory.volume,
        x ∈ Set.uIoc (0 : ℝ) (1/2) →
          (γ.concat δ h).integrand om x
            = deriv concatRepLeft x • γ.integrand om (concatRepLeft x) := by
      filter_upwards [h_almost_half] with x hx hx_uIoc
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1/2)] at hx_uIoc
      exact integrand_concat_of_mem_Ioo_left γ δ h om
        ⟨hx_uIoc.1, lt_of_le_of_ne hx_uIoc.2 hx⟩
    rw [intervalIntegral.integral_congr_ae h_congr_left]
    -- Step 2: substitution `u = concatRepLeft t` on `[0, 1/2]`.
    have h_concat_left_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) (1/2),
        HasDerivAt concatRepLeft (deriv concatRepLeft x) x := by
      intro x _
      exact (contDiff_concatRepLeft.differentiable (by decide) x).hasDerivAt
    have h_deriv_cont : ContinuousOn (deriv concatRepLeft)
        (Set.uIcc (0 : ℝ) (1/2)) :=
      (contDiff_concatRepLeft.continuous_deriv (by decide)).continuousOn
    have h_g_cont : Continuous (γ.integrand om) := γ.continuous_integrand om
    have h_sub := intervalIntegral.integral_deriv_smul_comp (f := concatRepLeft)
      (f' := deriv concatRepLeft) (g := γ.integrand om) (a := 0) (b := 1/2)
      h_concat_left_deriv h_deriv_cont h_g_cont
    -- `h_sub : ∫ x in 0..1/2, (deriv concatRepLeft x) • (γ.integrand om ∘ concatRepLeft) x
    --       = ∫ x in (concatRepLeft 0)..(concatRepLeft (1/2)), γ.integrand om x`.
    rw [show (fun x => deriv concatRepLeft x
              • γ.integrand om (concatRepLeft x))
            = fun x => deriv concatRepLeft x
                  • (γ.integrand om ∘ concatRepLeft) x from rfl]
    rw [h_sub, concatRepLeft_zero, concatRepLeft_half]
    rfl
  · -- Right half: symmetric, with `concatRepRight` and `δ`.
    have h_meas_one : MeasureTheory.volume ({1} : Set ℝ) = 0 :=
      Real.volume_singleton
    have h_almost_one : ∀ᵐ x ∂MeasureTheory.volume, x ≠ (1 : ℝ) := by
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{1}ᶜ, ?_, fun x hx => hx⟩
      rw [MeasureTheory.mem_ae_iff, compl_compl]
      exact h_meas_one
    have h_congr_right : ∀ᵐ x ∂MeasureTheory.volume,
        x ∈ Set.uIoc (1/2 : ℝ) 1 →
          (γ.concat δ h).integrand om x
            = deriv concatRepRight x • δ.integrand om (concatRepRight x) := by
      filter_upwards [h_almost_one] with x hx hx_uIoc
      rw [Set.uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at hx_uIoc
      exact integrand_concat_of_mem_Ioo_right γ δ h om
        ⟨hx_uIoc.1, lt_of_le_of_ne hx_uIoc.2 hx⟩
    rw [intervalIntegral.integral_congr_ae h_congr_right]
    have h_concat_right_deriv : ∀ x ∈ Set.uIcc (1/2 : ℝ) 1,
        HasDerivAt concatRepRight (deriv concatRepRight x) x := by
      intro x _
      exact (contDiff_concatRepRight.differentiable (by decide) x).hasDerivAt
    have h_deriv_cont : ContinuousOn (deriv concatRepRight)
        (Set.uIcc (1/2 : ℝ) 1) :=
      (contDiff_concatRepRight.continuous_deriv (by decide)).continuousOn
    have h_g_cont : Continuous (δ.integrand om) := δ.continuous_integrand om
    have h_sub := intervalIntegral.integral_deriv_smul_comp
      (f := concatRepRight) (f' := deriv concatRepRight)
      (g := δ.integrand om) (a := 1/2) (b := 1)
      h_concat_right_deriv h_deriv_cont h_g_cont
    rw [show (fun x => deriv concatRepRight x
              • δ.integrand om (concatRepRight x))
            = fun x => deriv concatRepRight x
                  • (δ.integrand om ∘ concatRepRight) x from rfl]
    rw [h_sub, concatRepRight_half, concatRepRight_one]
    rfl

end SmoothPath

end
