/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import JacobianChallenge.Analysis.PompeiuKernelPlaneIntegral
import JacobianChallenge.Analysis.PompeiuIntegrandIntegrability
import JacobianChallenge.Analysis.PompeiuKernelStokes
import JacobianChallenge.Analysis.PompeiuKernelRegularizedInv
import JacobianChallenge.Analysis.PompeiuKernelCutoff
import JacobianChallenge.Analysis.PompeiuKernel
import JacobianChallenge.Analysis.PompeiuKernelDirectionalIntegrand
import JacobianChallenge.Manifold.PartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-E (Section B+C): plane-form balance + DCT limit

Following Chip 3c-D's iterated balance equation:
```
∫ x in -L..L, ∫ y in -L..L,
  partialZBar α (x+y*I) · regInvSub z hε (x+y*I)
    + α (x+y*I) · partialZBar (regInvSub z hε) (x+y*I) = 0,
```
this file:

* Converts it to **plane (Bochner-over-ℂ) form** via the Fubini bridge
  `integral_complex_eq_iteratedIntegral_of_tsupport_in_ball` (Chip 3c-E
  Section A in `PompeiuKernelPlaneIntegral.lean`).
* Splits the plane integral into its two summands (both individually
  integrable).
* Takes the **DCT limit `ε → 0⁺` on the first summand**: as `ε → 0`,
  `regInvSub z hε ζ → (ζ - z)⁻¹` pointwise off `z`, dominated by
  `‖∂̄α(ζ)‖ · ‖(ζ-z)⁻¹‖` (integrable by Chip 1c). So
  ```
  ∫ ζ, ∂̄α ζ · regInvSub z hε ζ → ∫ ζ, ∂̄α ζ · (ζ - z)⁻¹.
  ```
  The right side is `-π · pompeiuKernel (∂̄α) z` by definition.

The second summand `∫ ζ, α · ∂̄(regInvSub z hε)` is the harder piece
(it requires a radial-bump calculation `ε² · scale + ψ' integration`).
That is Section D of Chip 3c-E (in `PompeiuKernelRadialBump.lean`).
After the second limit `→ π · α z`, combining with the balance closes
the Cauchy-Pompeiu identity.

## Main results

* `partialZBar_alpha_hasCompactSupport` — preservation of compact
  support under `partialZBar`.
* `integrable_partialZBar_mul_regInvSub` — integrability of the first
  summand for fixed `ε`.
* `integrable_alpha_mul_partialZBar_regInvSub` — integrability of the
  second summand for fixed `ε`.
* `balance_plane_eq_zero` — the plane-form of Chip 3c-D's balance
  equation, obtained by Fubini.
* `tendsto_integral_partialZBar_alpha_mul_regInvSub` — the DCT limit:
  ```
  Tendsto (fun ε => ∫ ζ, partialZBar α ζ · regularizedInvSub z hε ζ)
    (𝓝[>] 0) (𝓝 (∫ ζ, partialZBar α ζ · (ζ - z)⁻¹)).
  ```

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Real Topology Interval

namespace JacobianChallenge.PompeiuKernel

open JacobianChallenge

variable {α : ℂ → ℂ}

/-! ## Compact-support preservation under `partialZBar` -/

/-- `tsupport (partialZBar α) ⊆ tsupport α`, via mathlib's
`tsupport_fderiv_apply_subset` chain. (Repeated forward declaration —
see `tsupport_partialZBar_subset` below for the full proof.) -/
private lemma _tsupport_partialZBar_subset_aux (α : ℂ → ℂ) :
    tsupport (partialZBar α) ⊆ tsupport α := by
  have h1 : tsupport (fun ζ => (fderiv ℝ α ζ) 1) ⊆ tsupport α :=
    tsupport_fderiv_apply_subset ℝ 1
  have h_I : tsupport (fun ζ => (fderiv ℝ α ζ) I) ⊆ tsupport α :=
    tsupport_fderiv_apply_subset ℝ I
  have h_I_mul : tsupport (fun ζ => I * (fderiv ℝ α ζ) I) ⊆ tsupport α :=
    (tsupport_mul_subset_right (f := fun _ => I)
      (g := fun ζ => (fderiv ℝ α ζ) I)).trans h_I
  have h_sum : tsupport (fun ζ => (fderiv ℝ α ζ) 1 + I * (fderiv ℝ α ζ) I)
      ⊆ tsupport α :=
    (tsupport_add (fun ζ => (fderiv ℝ α ζ) 1)
        (fun ζ => I * (fderiv ℝ α ζ) I)).trans (Set.union_subset h1 h_I_mul)
  exact (tsupport_mul_subset_right (f := fun _ => (2 : ℂ)⁻¹)
      (g := fun ζ => (fderiv ℝ α ζ) 1 + I * (fderiv ℝ α ζ) I)).trans h_sum

/-- If `α` has compact support, so does `partialZBar α`. -/
lemma partialZBar_hasCompactSupport (h_supp : HasCompactSupport α) :
    HasCompactSupport (partialZBar α) :=
  h_supp.of_isClosed_subset (isClosed_tsupport _)
    (_tsupport_partialZBar_subset_aux α)

/-- `partialZBar α` is continuous when `α` is `C¹`. -/
lemma partialZBar_continuous (h_smooth : ContDiff ℝ 1 α) :
    Continuous (partialZBar α) := by
  have h_fderiv : Continuous (fderiv ℝ α) :=
    h_smooth.continuous_fderiv (by norm_num)
  have h_at_1 : Continuous (fun ζ => (fderiv ℝ α ζ) 1) :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp h_fderiv
  have h_at_I : Continuous (fun ζ => (fderiv ℝ α ζ) I) :=
    (ContinuousLinearMap.apply ℝ ℂ I).continuous.comp h_fderiv
  have h_combo : Continuous (fun ζ =>
      (fderiv ℝ α ζ) 1 + I * (fderiv ℝ α ζ) I) :=
    h_at_1.add (continuous_const.mul h_at_I)
  have h_target : Continuous (fun ζ =>
      (2 : ℂ)⁻¹ * ((fderiv ℝ α ζ) 1 + I * (fderiv ℝ α ζ) I)) :=
    continuous_const.mul h_combo
  exact h_target

/-! ## Support of the summands -/

/-- `tsupport (partialZBar α · regularizedInvSub z hε) ⊆ tsupport α`.
The first factor is supported in `tsupport α` (via
`partialZBar_hasCompactSupport` reasoning), and the product is supported
in the support of the first factor. -/
lemma tsupport_partialZBar_alpha_mul_regInvSub_subset
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ)
      ⊆ tsupport (partialZBar α) := by
  apply closure_mono
  intro ζ hζ
  rw [Function.mem_support] at hζ ⊢
  intro h_zero
  apply hζ
  rw [h_zero, zero_mul]

/-- `tsupport (α · partialZBar (regularizedInvSub z hε)) ⊆ tsupport α`. -/
lemma tsupport_alpha_mul_partialZBar_regInvSub_subset
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun ζ => α ζ * partialZBar (regularizedInvSub z hε) ζ)
      ⊆ tsupport α := by
  apply closure_mono
  intro ζ hζ
  rw [Function.mem_support] at hζ ⊢
  intro h_zero
  apply hζ
  rw [h_zero, zero_mul]

/-! ## Integrability of the two summands -/

/-- `partialZBar α · regularizedInvSub z hε` is continuous (as a product
of continuous functions). -/
lemma continuous_partialZBar_alpha_mul_regInvSub
    (h_smooth : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ) := by
  have h_pZ : Continuous (partialZBar α) := partialZBar_continuous h_smooth
  have h_g : Continuous (regularizedInvSub z hε) :=
    (regularizedInvSub_contDiff z hε (n := 0)).continuous
  exact h_pZ.mul h_g

/-- The first summand has compact support (product of compactly
supported function with bounded one). -/
lemma hasCompactSupport_partialZBar_alpha_mul_regInvSub
    (h_supp : HasCompactSupport α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ) :=
  (partialZBar_hasCompactSupport h_supp).mul_right

/-- The first summand is integrable. -/
lemma integrable_partialZBar_mul_regInvSub
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ) := by
  apply (continuous_partialZBar_alpha_mul_regInvSub h_smooth z hε).integrable_of_hasCompactSupport
  exact hasCompactSupport_partialZBar_alpha_mul_regInvSub h_supp z hε

/-- `α · partialZBar (regularizedInvSub z hε)` is continuous. -/
lemma continuous_alpha_mul_partialZBar_regInvSub
    (h_smooth : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun ζ => α ζ * partialZBar (regularizedInvSub z hε) ζ) := by
  have h_α : Continuous α := h_smooth.continuous
  have h_g_smooth : ContDiff ℝ 1 (regularizedInvSub z hε) :=
    regularizedInvSub_contDiff z hε
  have h_pZ_g : Continuous (partialZBar (regularizedInvSub z hε)) :=
    partialZBar_continuous h_g_smooth
  exact h_α.mul h_pZ_g

/-- The second summand has compact support. -/
lemma hasCompactSupport_alpha_mul_partialZBar_regInvSub
    (h_supp : HasCompactSupport α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fun ζ => α ζ * partialZBar (regularizedInvSub z hε) ζ) :=
  h_supp.mul_right

/-- The second summand is integrable. -/
lemma integrable_alpha_mul_partialZBar_regInvSub
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ζ => α ζ * partialZBar (regularizedInvSub z hε) ζ) := by
  apply (continuous_alpha_mul_partialZBar_regInvSub h_smooth z hε).integrable_of_hasCompactSupport
  exact hasCompactSupport_alpha_mul_partialZBar_regInvSub h_supp z hε

/-! ## Plane-form balance equation -/

/-- Sum-of-summands integrability. -/
lemma integrable_balance_integrand
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ
      + α ζ * partialZBar (regularizedInvSub z hε) ζ) :=
  (integrable_partialZBar_mul_regInvSub h_smooth h_supp z hε).add
    (integrable_alpha_mul_partialZBar_regInvSub h_smooth h_supp z hε)

/-- `tsupport (partialZBar α) ⊆ tsupport α`. -/
lemma tsupport_partialZBar_subset (α : ℂ → ℂ) :
    tsupport (partialZBar α) ⊆ tsupport α :=
  _tsupport_partialZBar_subset_aux α

/-- Support of the sum is in `tsupport α`. -/
lemma tsupport_balance_integrand_subset
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ
        + α ζ * partialZBar (regularizedInvSub z hε) ζ)
      ⊆ tsupport α := by
  have h_first : tsupport (fun ζ => partialZBar α ζ * regularizedInvSub z hε ζ)
      ⊆ tsupport α :=
    tsupport_mul_subset_left.trans (tsupport_partialZBar_subset α)
  have h_second : tsupport (fun ζ => α ζ * partialZBar (regularizedInvSub z hε) ζ)
      ⊆ tsupport α :=
    tsupport_mul_subset_left
  exact (tsupport_add _ _).trans (Set.union_subset h_first h_second)

/-- **Plane-form balance equation (Chip 3c-E Section B).** Combines
Chip 3c-D's iterated balance with the Fubini bridge to yield the
Bochner-integral form on `ℂ`. -/
theorem balance_plane_eq_zero
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL_pos : 0 < L) (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
    ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSub z hε ζ
        + α ζ * partialZBar (regularizedInvSub z hε) ζ = 0 := by
  -- Apply Chip 3c-D's iterated balance.
  have h_iter := balance_iteratedIntegral_eq_zero h_smooth z hε hL_pos hL_supp
  -- Apply the Fubini bridge.
  have h_supp_sum : tsupport (fun ζ =>
        partialZBar α ζ * regularizedInvSub z hε ζ
          + α ζ * partialZBar (regularizedInvSub z hε) ζ)
      ⊆ Metric.ball 0 L :=
    (tsupport_balance_integrand_subset α z hε).trans hL_supp
  have h_int_sum := integrable_balance_integrand h_smooth h_supp z hε
  rw [integral_complex_eq_iteratedIntegral_of_tsupport_in_ball h_int_sum hL_pos h_supp_sum]
  exact h_iter

/-! ## Section C: DCT limit `ε → 0⁺` of the first summand -/

/-- Wrapper that turns the dependent `regularizedInvSub z hε` into a
function of `ε : ℝ` by defaulting to `(·-z)⁻¹` when `ε ≤ 0`. This
matches the DCT pointwise limit on positive `ε`, letting us state the
`Tendsto` limit over the filter `𝓝[>] (0 : ℝ)`. -/
noncomputable def regularizedInvSubReal (z : ℂ) (ε : ℝ) : ℂ → ℂ :=
  if h : 0 < ε then regularizedInvSub z h else fun ζ => (ζ - z)⁻¹

/-- On `0 < ε`, the wrapper agrees with `regularizedInvSub z hε`. -/
lemma regularizedInvSubReal_of_pos {z : ℂ} {ε : ℝ} (hε : 0 < ε) :
    regularizedInvSubReal z ε = regularizedInvSub z hε := by
  unfold regularizedInvSubReal; rw [dif_pos hε]

/-- Pointwise eventual equality: for `ζ ≠ z`, the regularized inverse
factor equals `(ζ-z)⁻¹` for all small enough `ε > 0`. -/
lemma regularizedInvSub_eventuallyEq_of_ne (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), regularizedInvSubReal z ε ζ = (ζ - z)⁻¹ := by
  have h_dist_pos : 0 < dist ζ z := dist_pos.mpr hζ
  -- For `0 < ε < dist ζ z`, `ζ ∉ ball z ε`, so `pompeiuCutoff z hε ζ = 1`,
  -- so `regularizedInvSub z hε ζ = (ζ-z)⁻¹`.
  have h_small : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < dist ζ z :=
    eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds h_dist_pos)
  filter_upwards [h_small, self_mem_nhdsWithin] with ε hε hε_pos
  -- `hε_pos : ε ∈ Set.Ioi 0`, i.e., `0 < ε`.
  have hε' : 0 < ε := hε_pos
  -- ζ ∉ ball z ε.
  have h_notMem : ζ ∉ Metric.ball z ε := by
    rw [Metric.mem_ball]; linarith
  -- pompeiuCutoff z hε' ζ = 1.
  have h_cutoff : pompeiuCutoff z hε' ζ = 1 :=
    pompeiuCutoff_eq_one_of_not_mem_ball z hε' h_notMem
  -- Unfold.
  rw [regularizedInvSubReal_of_pos hε']
  show (ζ - z)⁻¹ * ((pompeiuCutoff z hε' ζ : ℝ) : ℂ) = (ζ - z)⁻¹
  rw [h_cutoff]; push_cast; ring

/-- `regularizedInvSubReal z ε ζ → (ζ-z)⁻¹` as `ε → 0⁺`, for any `ζ ≠ z`. -/
lemma tendsto_regularizedInvSubReal_of_ne (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    Tendsto (fun ε : ℝ => regularizedInvSubReal z ε ζ)
      (𝓝[>] (0 : ℝ)) (𝓝 ((ζ - z)⁻¹)) := by
  -- Eventually `regularizedInvSubReal z ε ζ = (ζ - z)⁻¹`, so the limit
  -- is the constant `(ζ - z)⁻¹`.
  have h_eq : (fun ε : ℝ => regularizedInvSubReal z ε ζ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => (ζ - z)⁻¹) :=
    regularizedInvSub_eventuallyEq_of_ne z hζ
  exact (Filter.tendsto_congr' h_eq).mpr tendsto_const_nhds

/-- Norm bound on the regularized inverse factor: `‖regInvSub z hε ζ‖ ≤ ‖(ζ-z)⁻¹‖`. -/
lemma norm_regularizedInvSub_le (z : ℂ) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    ‖regularizedInvSub z hε ζ‖ ≤ ‖(ζ - z)⁻¹‖ := by
  show ‖(ζ - z)⁻¹ * ((pompeiuCutoff z hε ζ : ℝ) : ℂ)‖ ≤ ‖(ζ - z)⁻¹‖
  rw [norm_mul]
  have h_cutoff_nonneg : 0 ≤ pompeiuCutoff z hε ζ := pompeiuCutoff_nonneg z hε ζ
  have h_cutoff_le_one : pompeiuCutoff z hε ζ ≤ 1 := pompeiuCutoff_le_one z hε ζ
  have h_cast : ‖((pompeiuCutoff z hε ζ : ℝ) : ℂ)‖ = pompeiuCutoff z hε ζ := by
    rw [Complex.norm_real]; exact abs_of_nonneg h_cutoff_nonneg
  rw [h_cast]
  nlinarith [norm_nonneg ((ζ - z)⁻¹)]

/-- Norm bound on the first balance summand:
`‖partialZBar α ζ · regInvSub z hε ζ‖ ≤ ‖partialZBar α ζ‖ · ‖(ζ-z)⁻¹‖`. -/
lemma norm_partialZBar_mul_regInvSub_le
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    ‖partialZBar α ζ * regularizedInvSub z hε ζ‖
      ≤ ‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖ := by
  rw [norm_mul]
  have h := norm_regularizedInvSub_le z hε ζ
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- Integrability of the DCT dominator `‖partialZBar α ζ‖ · ‖(ζ-z)⁻¹‖`,
via Chip 1c's `integrable_pompeiuIntegrand_of_continuous_hasCompactSupport`
applied to `partialZBar α`. -/
lemma integrable_dominator_partialZBar
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Integrable (fun ζ => ‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖) := by
  have h_pZ_cont : Continuous (partialZBar α) := partialZBar_continuous h_smooth
  have h_pZ_supp : HasCompactSupport (partialZBar α) :=
    partialZBar_hasCompactSupport h_supp
  -- Chip 1c gives integrability of `pompeiuIntegrand (partialZBar α) z`.
  have h_int : Integrable (pompeiuIntegrand (partialZBar α) z) :=
    integrable_pompeiuIntegrand_of_continuous_hasCompactSupport h_pZ_cont h_pZ_supp z
  -- The norm of an integrable function is integrable. Its pointwise form
  -- here is `‖partialZBar α ζ * (ζ-z)⁻¹‖ = ‖partialZBar α ζ‖ * ‖(ζ-z)⁻¹‖`.
  have h_norm_int : Integrable (fun ζ => ‖pompeiuIntegrand (partialZBar α) z ζ‖) :=
    h_int.norm
  convert h_norm_int using 1
  funext ζ
  show ‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖ = ‖partialZBar α ζ * (ζ - z)⁻¹‖
  rw [norm_mul]

/-- **DCT limit (Chip 3c-E Section C).** As `ε → 0⁺`,
```
∫ ζ : ℂ, partialZBar α ζ · regInvSub z hε ζ
  → ∫ ζ : ℂ, partialZBar α ζ · (ζ - z)⁻¹.
```
The right-hand side is `-π · pompeiuKernel (partialZBar α) z` by
definition of `pompeiuKernel`. -/
theorem tendsto_integral_partialZBar_alpha_mul_regInvSub
    (h_smooth : ContDiff ℝ 1 α) (h_supp : HasCompactSupport α) (z : ℂ) :
    Tendsto (fun ε : ℝ =>
        ∫ ζ : ℂ, partialZBar α ζ * regularizedInvSubReal z ε ζ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ζ : ℂ, partialZBar α ζ * (ζ - z)⁻¹)) := by
  -- Apply mathlib's DCT for filters.
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun ζ => ‖partialZBar α ζ‖ * ‖(ζ - z)⁻¹‖) ?_ ?_ ?_ ?_
  · -- AEStronglyMeasurable for ε > 0.
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε' : 0 < ε := hε_pos
    rw [regularizedInvSubReal_of_pos hε']
    exact ((partialZBar_continuous h_smooth).aestronglyMeasurable.mul
        (regularizedInvSub_contDiff z hε' (n := 0)).continuous.aestronglyMeasurable)
  · -- Norm bound for ε > 0.
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    have hε' : 0 < ε := hε_pos
    refine Filter.Eventually.of_forall (fun ζ => ?_)
    rw [regularizedInvSubReal_of_pos hε']
    exact norm_partialZBar_mul_regInvSub_le α z hε' ζ
  · -- Integrability of the dominator.
    exact integrable_dominator_partialZBar h_smooth h_supp z
  · -- Pointwise convergence. At `ζ ≠ z`, wrapper eventually = `(ζ-z)⁻¹`.
    -- At `ζ = z`, both sides are `0`: `(z-z)⁻¹ = 0⁻¹ = 0` in `ℂ`, and
    -- `regularizedInvSub z hε z = 0 * 0 = 0`.
    refine Filter.Eventually.of_forall (fun ζ => ?_)
    by_cases hζ : ζ = z
    · -- `ζ = z`: both function values and limit value are `0`.
      -- `(ζ-z)⁻¹ = 0` since ζ-z = 0 and 0⁻¹ = 0 in ℂ.
      -- `regularizedInvSubReal z ε ζ` is also 0 (both branches).
      have h_lim_zero : partialZBar α ζ * (ζ - z)⁻¹ = 0 := by
        rw [hζ]; simp
      rw [h_lim_zero]
      have h_F_zero : ∀ ε : ℝ, partialZBar α ζ * regularizedInvSubReal z ε ζ = 0 := by
        intro ε
        unfold regularizedInvSubReal
        split_ifs with hε'
        · -- 0 < ε: regularizedInvSub z hε' ζ = 0 since pompeiuCutoff = 0 at ζ=z.
          show partialZBar α ζ * ((ζ - z)⁻¹ * ((pompeiuCutoff z hε' ζ : ℝ) : ℂ)) = 0
          rw [hζ]; simp
        · -- ε ≤ 0: defaults to (ζ-z)⁻¹.
          rw [hζ]; simp
      simp_rw [h_F_zero]
      exact tendsto_const_nhds
    · -- `ζ ≠ z`: wrapper eventually equals `(ζ-z)⁻¹`.
      have h_tendsto :
          Tendsto (fun ε : ℝ => regularizedInvSubReal z ε ζ)
            (𝓝[>] (0 : ℝ)) (𝓝 ((ζ - z)⁻¹)) :=
        tendsto_regularizedInvSubReal_of_ne z hζ
      exact h_tendsto.const_mul (partialZBar α ζ)

end JacobianChallenge.PompeiuKernel

end
