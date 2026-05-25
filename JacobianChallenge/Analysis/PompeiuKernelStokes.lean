/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JacobianChallenge.Analysis.PompeiuKernelRegularizedInv
import JacobianChallenge.Manifold.PartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-D: Stokes' theorem for `∂̄` on cs `C¹`

This file proves the **Stokes-for-`∂̄`** identity

```
∫ x in -L..L, ∫ y in -L..L, partialZBar f (x + y * I) = 0
```

for any compactly-supported `C¹` function `f : ℂ → ℂ` whose `tsupport`
fits inside `Metric.ball 0 L`. The proof is mathlib's rectangle Stokes
(`Complex.integral_boundary_rect_of_differentiableOn_real`,
`Analysis/Complex/CauchyIntegral.lean:251`) plus the vanishing of all
four boundary line integrals (by compact support of `f`).

The integrand `I • fderiv ℝ f x 1 - fderiv ℝ f x I` that mathlib's
rectangle Stokes produces equals `2 * I * partialZBar f x` pointwise (a
direct algebraic identity from the Wirtinger definition of
`partialZBar`).

## Chip 3 arc context

* Chip 3a — small-disc limit `∮_{C(z,ε)} α(ζ)·(ζ-z)⁻¹ dζ → 2πI · α(z)`.
* Chip 3b — algebraic bridge
  `partialZBar (pompeiuKernel α) = pompeiuKernel (partialZBar α)`.
* Chip 3c-A — pointwise `partialZBar` reduction off `z`.
* Chip 3c-B — `HasFDerivAt` for `α · (·-z)⁻¹` off `z`.
* Chip 3c-C₁ — smooth cutoff `pompeiuCutoff z ε`.
* Chip 3c-C₂ — regularized inverse factor `regularizedInvSub`.
* **Chip 3c-D (this file)** — Stokes-for-`∂̄`.
* Chip 3c-E (next) — apply to `α · regularizedInvSub z hε`, Leibniz
  split, extend to full-plane integral, get balance equation.
* Chip 3c-F — DCT limit `ε → 0` + Chip 3a → final identity.

## Main results

* `partialZBar_eq_integrand_div_two_I` — algebraic identity
  `I • fderiv ℝ f x 1 - fderiv ℝ f x I = 2 * I * partialZBar f x`.
* `iteratedIntegral_partialZBar_eq_zero` — Stokes-for-`∂̄` on cs `C¹`.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Real Topology Interval

namespace JacobianChallenge.PompeiuKernel

/-! ## Algebraic identity relating mathlib's rect-Stokes integrand to `partialZBar` -/

/-- Pointwise algebraic identity:
`I • fderiv ℝ f x 1 - fderiv ℝ f x I = 2 * I * partialZBar f x`.

This converts the integrand in mathlib's rectangle Stokes conclusion
into the Wirtinger `∂̄`. -/
lemma partialZBar_eq_integrand_div_two_I (f : ℂ → ℂ) (x : ℂ) :
    I • (fderiv ℝ f x) 1 - (fderiv ℝ f x) I = 2 * I * partialZBar f x := by
  unfold partialZBar
  show I * (fderiv ℝ f x) 1 - (fderiv ℝ f x) I
    = 2 * I * ((2 : ℂ)⁻¹ * ((fderiv ℝ f x) 1 + I * (fderiv ℝ f x) I))
  set a : ℂ := (fderiv ℝ f x) 1
  set b : ℂ := (fderiv ℝ f x) I
  have hII : (I : ℂ) * I = -1 := I_mul_I
  have h2 : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
  calc I * a - b
      = I * a + (I * I) * b := by rw [hII]; ring
    _ = I * (a + I * b) := by ring
    _ = 1 * (I * (a + I * b)) := by rw [one_mul]
    _ = (2 * (2 : ℂ)⁻¹) * (I * (a + I * b)) := by rw [h2]
    _ = 2 * I * ((2 : ℂ)⁻¹ * (a + I * b)) := by ring

/-! ## Compact-support helpers -/

/-- If `tsupport f ⊆ ball 0 L`, then `f ζ = 0` whenever `‖ζ‖ ≥ L`. -/
lemma eq_zero_of_norm_ge_of_tsupport_subset_ball
    {f : ℂ → ℂ} {L : ℝ}
    (h_supp : tsupport f ⊆ Metric.ball 0 L)
    {ζ : ℂ} (hζ : L ≤ ‖ζ‖) :
    f ζ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h_mem
  have := h_supp h_mem
  rw [Metric.mem_ball, dist_zero_right] at this
  linarith

/-- Norm bound for horizontal lines: for `c : ℝ` with `|c| ≥ L`, every
point `x + c * I` has norm `≥ L`. -/
lemma norm_horiz_ge (x c : ℝ) {L : ℝ} (hL_pos : 0 < L) (hc : L ≤ |c|) :
    L ≤ ‖((x : ℂ) + c * I)‖ := by
  rw [Complex.norm_add_mul_I]
  calc L = Real.sqrt (L ^ 2) := by rw [Real.sqrt_sq hL_pos.le]
    _ ≤ Real.sqrt (c ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hc2 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
        rw [hc2]; nlinarith
    _ ≤ Real.sqrt (x ^ 2 + c ^ 2) := by
        apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg x]

/-- Norm bound for vertical lines: for `c : ℝ` with `|c| ≥ L`, every
point `c + y * I` has norm `≥ L`. -/
lemma norm_vert_ge (y c : ℝ) {L : ℝ} (hL_pos : 0 < L) (hc : L ≤ |c|) :
    L ≤ ‖((c : ℂ) + y * I)‖ := by
  rw [Complex.norm_add_mul_I]
  calc L = Real.sqrt (L ^ 2) := by rw [Real.sqrt_sq hL_pos.le]
    _ ≤ Real.sqrt (c ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hc2 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
        rw [hc2]; nlinarith
    _ ≤ Real.sqrt (c ^ 2 + y ^ 2) := by
        apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg y]

/-- Interval-integral congruence to zero on a horizontal line. -/
lemma intervalIntegral_zero_on_uIcc_horiz {f : ℂ → ℂ}
    (a b : ℝ) (c : ℝ)
    (h_zero : ∀ x ∈ Set.uIcc a b, f ((x : ℂ) + c * I) = 0) :
    ∫ x in a..b, f ((x : ℂ) + c * I) = 0 := by
  calc (∫ x in a..b, f ((x : ℂ) + c * I))
      = ∫ _ in a..b, (0 : ℂ) :=
        intervalIntegral.integral_congr (fun x hx => h_zero x hx)
    _ = 0 := intervalIntegral.integral_zero

/-- Interval-integral congruence to zero on a vertical line. -/
lemma intervalIntegral_zero_on_uIcc_vert {f : ℂ → ℂ}
    (a b : ℝ) (c : ℝ)
    (h_zero : ∀ y ∈ Set.uIcc a b, f ((c : ℂ) + y * I) = 0) :
    ∫ y in a..b, f ((c : ℂ) + y * I) = 0 := by
  calc (∫ y in a..b, f ((c : ℂ) + y * I))
      = ∫ _ in a..b, (0 : ℂ) :=
        intervalIntegral.integral_congr (fun y hy => h_zero y hy)
    _ = 0 := intervalIntegral.integral_zero

/-! ## Main Stokes-for-`∂̄` theorem -/

/-- **Stokes-for-`∂̄` on compactly-supported `C¹` functions
(Chip 3c-D main).** For any `f : ℂ → ℂ` of class `C¹` whose
`tsupport` fits in `Metric.ball 0 L`,

```
∫ x in -L..L, ∫ y in -L..L, partialZBar f (x + y * I) = 0.
```

Proof: apply mathlib's
`Complex.integral_boundary_rect_of_differentiableOn_real` on the
square rectangle `[-L, L]²`. All four boundary line integrals vanish
because `f` is zero on the rectangle boundary (every boundary point
has Euclidean norm `≥ L`). The remaining iterated integral is then
identified with the iterated integral of `2 * I * partialZBar f`
via `partialZBar_eq_integrand_div_two_I`, and dividing by the nonzero
scalar `2 * I` gives the conclusion. -/
theorem iteratedIntegral_partialZBar_eq_zero
    {f : ℂ → ℂ} (h_smooth : ContDiff ℝ 1 f)
    {L : ℝ} (hL_pos : 0 < L)
    (hL_supp : tsupport f ⊆ Metric.ball 0 L) :
    ∫ x in -L..L, ∫ y in -L..L, partialZBar f ((x : ℂ) + y * I) = 0 := by
  -- Rectangle corners.
  set z₀ : ℂ := (-L : ℂ) + (-L : ℂ) * I with hz₀
  set w₀ : ℂ := (L : ℂ) + (L : ℂ) * I with hw₀
  have hz₀_re : z₀.re = -L := by simp [z₀]
  have hz₀_im : z₀.im = -L := by simp [z₀]
  have hw₀_re : w₀.re = L := by simp [w₀]
  have hw₀_im : w₀.im = L := by simp [w₀]
  -- Differentiability and integrability hypotheses for rect Stokes.
  have h1_ne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have h_diff : Differentiable ℝ f := h_smooth.differentiable h1_ne
  have h_diffOn : DifferentiableOn ℝ f
      ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) :=
    h_diff.differentiableOn
  have h_fderiv_cont : Continuous (fderiv ℝ f) :=
    h_smooth.continuous_fderiv h1_ne
  have h_integrand_cont : Continuous (fun x : ℂ =>
      I • (fderiv ℝ f x) 1 - (fderiv ℝ f x) I) := by
    refine Continuous.sub ?_ ?_
    · exact continuous_const.smul
        ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp h_fderiv_cont)
    · exact (ContinuousLinearMap.apply ℝ ℂ I).continuous.comp h_fderiv_cont
  have h_rect_compact :
      IsCompact (([[z₀.re, w₀.re]] : Set ℝ) ×ℂ [[z₀.im, w₀.im]]) :=
    IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  have h_integrable : IntegrableOn
      (fun x : ℂ => I • (fderiv ℝ f x) 1 - (fderiv ℝ f x) I)
      ([[z₀.re, w₀.re]] ×ℂ [[z₀.im, w₀.im]]) :=
    h_integrand_cont.continuousOn.integrableOn_compact h_rect_compact
  -- Apply mathlib's rectangle Stokes.
  have h_stokes := Complex.integral_boundary_rect_of_differentiableOn_real
    f z₀ w₀ h_diffOn h_integrable
  -- Boundary line integrals — each is zero by compact support of f.
  have hL_zero : ∀ ζ : ℂ, L ≤ ‖ζ‖ → f ζ = 0 := fun ζ hζ =>
    eq_zero_of_norm_ge_of_tsupport_subset_ball hL_supp hζ
  have h_abs_neg_L : |(-L : ℝ)| = L := by rw [abs_neg]; exact abs_of_pos hL_pos
  have h_abs_L : |L| = L := abs_of_pos hL_pos
  have h_bot : (∫ x : ℝ in z₀.re..w₀.re, f ((x : ℂ) + z₀.im * I)) = 0 := by
    rw [hz₀_im]
    apply intervalIntegral_zero_on_uIcc_horiz
    intro x _
    exact hL_zero _ (norm_horiz_ge x (-L) hL_pos h_abs_neg_L.ge)
  have h_top : (∫ x : ℝ in z₀.re..w₀.re, f ((x : ℂ) + w₀.im * I)) = 0 := by
    rw [hw₀_im]
    apply intervalIntegral_zero_on_uIcc_horiz
    intro x _
    exact hL_zero _ (norm_horiz_ge x L hL_pos h_abs_L.ge)
  have h_right : (∫ y : ℝ in z₀.im..w₀.im, f ((w₀.re : ℂ) + y * I)) = 0 := by
    rw [hw₀_re]
    apply intervalIntegral_zero_on_uIcc_vert
    intro y _
    exact hL_zero _ (norm_vert_ge y L hL_pos h_abs_L.ge)
  have h_left : (∫ y : ℝ in z₀.im..w₀.im, f ((z₀.re : ℂ) + y * I)) = 0 := by
    rw [hz₀_re]
    apply intervalIntegral_zero_on_uIcc_vert
    intro y _
    exact hL_zero _ (norm_vert_ge y (-L) hL_pos h_abs_neg_L.ge)
  -- Combine boundary vanishings: LHS of rect Stokes = 0.
  rw [h_bot, h_top, h_right, h_left] at h_stokes
  simp only [sub_zero, smul_zero, add_zero] at h_stokes
  -- Rewrite the iterated integrand using partialZBar.
  rw [hz₀_re, hw₀_re, hz₀_im, hw₀_im] at h_stokes
  have h_step1 :
      (∫ x : ℝ in -L..L, ∫ y : ℝ in -L..L,
          I • (fderiv ℝ f ((x : ℂ) + y * I)) 1
            - (fderiv ℝ f ((x : ℂ) + y * I)) I)
        = ∫ x : ℝ in -L..L,
            ∫ y : ℝ in -L..L, 2 * I * partialZBar f ((x : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    exact partialZBar_eq_integrand_div_two_I f ((x : ℂ) + y * I)
  rw [h_step1] at h_stokes
  -- Pull constant 2 * I out of both interval integrals.
  have h_step2 :
      (∫ x : ℝ in -L..L, ∫ y : ℝ in -L..L,
          2 * I * partialZBar f ((x : ℂ) + y * I))
        = 2 * I * ∫ x : ℝ in -L..L, ∫ y : ℝ in -L..L,
            partialZBar f ((x : ℂ) + y * I) := by
    have h_inner : ∀ x : ℝ,
        (∫ y in (-L : ℝ)..L, 2 * I * partialZBar f ((x : ℂ) + y * I))
          = 2 * I * ∫ y in (-L : ℝ)..L, partialZBar f ((x : ℂ) + y * I) :=
      fun x => intervalIntegral.integral_const_mul (2 * I) _
    calc (∫ x : ℝ in -L..L, ∫ y : ℝ in -L..L,
              2 * I * partialZBar f ((x : ℂ) + y * I))
        = ∫ x : ℝ in -L..L, 2 * I *
              ∫ y : ℝ in -L..L, partialZBar f ((x : ℂ) + y * I) := by
            apply intervalIntegral.integral_congr
            intro x _
            exact h_inner x
      _ = 2 * I * ∫ x : ℝ in -L..L, ∫ y : ℝ in -L..L,
              partialZBar f ((x : ℂ) + y * I) :=
          intervalIntegral.integral_const_mul (2 * I) _
  rw [h_step2] at h_stokes
  -- h_stokes : 0 = 2 * I * (target integral). Divide by 2 * I (nonzero).
  have h_2I_ne : (2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have h_eq : 2 * I * (∫ x : ℝ in -L..L, ∫ y : ℝ in -L..L,
      partialZBar f ((x : ℂ) + y * I)) = 0 := h_stokes.symm
  rcases mul_eq_zero.mp h_eq with h | h
  · exact absurd h h_2I_ne
  · exact h

/-! ## Application: balance equation for the regularized Pompeiu integrand

We apply `iteratedIntegral_partialZBar_eq_zero` to
`f(η) := α(η) * regularizedInvSub z hε η` and use Leibniz to split
the resulting integral into the **balance equation**:

```
∫∫ partialZBar α (·) · regularizedInvSub z hε (·)
  + ∫∫ α (·) · partialZBar (regularizedInvSub z hε) (·) = 0.
```

This is the iterated-integral form of the integration-by-parts step in
the Cauchy-Pompeiu argument. The DCT-limit `ε → 0` (Chip 3c-F) will
then identify each integral with its full-plane counterpart and use
Chip 3a's small-disc limit to extract `α z`. -/

/-- `α * regularizedInvSub z hε` is `C¹` when `α` is `C¹`. -/
lemma contDiff_alpha_mul_regInvSub
    {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fun η => α η * regularizedInvSub z hε η) :=
  h_α.mul (regularizedInvSub_contDiff z hε)

/-- The support of `α * regularizedInvSub z hε` is contained in the
support of `α`, hence compact when `α` has compact support. -/
lemma hasCompactSupport_alpha_mul_regInvSub
    {α : ℂ → ℂ} (h_supp : HasCompactSupport α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (fun η => α η * regularizedInvSub z hε η) :=
  h_supp.mul_right

/-- `tsupport (α * regularizedInvSub z hε) ⊆ tsupport α`. -/
lemma tsupport_alpha_mul_regInvSub_subset
    (α : ℂ → ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (fun η => α η * regularizedInvSub z hε η) ⊆ tsupport α := by
  apply closure_mono
  intro η hη
  rw [Function.mem_support] at hη ⊢
  intro h_zero
  apply hη
  rw [h_zero, zero_mul]

/-- Pointwise Leibniz expansion of `partialZBar (α * g_ε)`. Uses the
existing `partialZBar_mul` from `Manifold/PartialZBar.lean`. -/
lemma partialZBar_alpha_mul_regInvSub
    {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    partialZBar (fun η => α η * regularizedInvSub z hε η) ζ
      = partialZBar α ζ * regularizedInvSub z hε ζ
        + α ζ * partialZBar (regularizedInvSub z hε) ζ := by
  have h_α_diff : DifferentiableAt ℝ α ζ :=
    (h_α.differentiable (by norm_num)).differentiableAt
  have h_g_contDiff : ContDiff ℝ (1 : ℕ∞) (regularizedInvSub z hε) :=
    regularizedInvSub_contDiff z hε
  have h_g_diff : DifferentiableAt ℝ (regularizedInvSub z hε) ζ :=
    (h_g_contDiff.differentiable (by norm_num)).differentiableAt
  -- partialZBar_mul applies pointwise to `α * g`.
  have h_mul := partialZBar_mul h_α_diff h_g_diff
  show partialZBar ((α : ℂ → ℂ) * (regularizedInvSub z hε)) ζ
        = partialZBar α ζ * regularizedInvSub z hε ζ
          + α ζ * partialZBar (regularizedInvSub z hε) ζ
  exact h_mul

/-- **Balance equation for the regularized Pompeiu integrand
(Chip 3c-D application).** For `α : ℂ → ℂ` of class `C¹` with compact
support whose `tsupport` is contained in `Metric.ball 0 L`,

```
∫ x in -L..L, ∫ y in -L..L,
  partialZBar α (x + y*I) * regularizedInvSub z hε (x + y*I)
    + α (x + y*I) * partialZBar (regularizedInvSub z hε) (x + y*I) = 0.
```

This is the iterated-integral form of integration-by-parts in the
Cauchy-Pompeiu argument. -/
theorem balance_iteratedIntegral_eq_zero
    {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL_pos : 0 < L)
    (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
    ∫ x in -L..L, ∫ y in -L..L,
      partialZBar α ((x : ℂ) + y * I) * regularizedInvSub z hε ((x : ℂ) + y * I)
        + α ((x : ℂ) + y * I)
            * partialZBar (regularizedInvSub z hε) ((x : ℂ) + y * I)
      = 0 := by
  -- Set f := α * g_ε. Then f is C¹, compactly supported (since α is),
  -- and tsupport f ⊆ tsupport α ⊆ ball 0 L.
  set f : ℂ → ℂ := fun η => α η * regularizedInvSub z hε η with hf_def
  have h_f_smooth : ContDiff ℝ 1 f := contDiff_alpha_mul_regInvSub h_α z hε
  have h_f_supp : tsupport f ⊆ Metric.ball 0 L :=
    (tsupport_alpha_mul_regInvSub_subset α z hε).trans hL_supp
  -- Apply Stokes-for-∂̄.
  have h_stokes := iteratedIntegral_partialZBar_eq_zero h_f_smooth hL_pos h_f_supp
  -- Rewrite the integrand using Leibniz.
  have h_pointwise : ∀ ζ : ℂ,
      partialZBar f ζ
        = partialZBar α ζ * regularizedInvSub z hε ζ
          + α ζ * partialZBar (regularizedInvSub z hε) ζ :=
    fun ζ => partialZBar_alpha_mul_regInvSub h_α z hε ζ
  -- Transport the rewrite into the iterated integral.
  have h_rewrite :
      (∫ x in -L..L, ∫ y in -L..L, partialZBar f ((x : ℂ) + y * I))
        = ∫ x in -L..L, ∫ y in -L..L,
            partialZBar α ((x : ℂ) + y * I) * regularizedInvSub z hε ((x : ℂ) + y * I)
              + α ((x : ℂ) + y * I)
                  * partialZBar (regularizedInvSub z hε) ((x : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    exact h_pointwise ((x : ℂ) + y * I)
  rw [h_rewrite] at h_stokes
  exact h_stokes

end JacobianChallenge.PompeiuKernel
