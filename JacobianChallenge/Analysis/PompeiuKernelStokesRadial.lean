/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PompeiuKernelStokes
import JacobianChallenge.Analysis.PompeiuKernelRegularizedInvRadial

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F-3b: radial-cutoff Stokes balance

This file replays Chip 3c-D's `balance_iteratedIntegral_eq_zero` for
the radial-cutoff regularized inverse `regularizedInvSubRadial`. The
proof is identical line-for-line: the generic Stokes-for-`∂̄` theorem
`iteratedIntegral_partialZBar_eq_zero` (Chip 3c-D, file
`PompeiuKernelStokes.lean`) is applied to `α · regularizedInvSubRadial`,
the Leibniz expansion `partialZBar_mul` (from `Manifold/PartialZBar.lean`)
splits the integrand, and compact support of `α` carries through
multiplication on the right.

The reason we re-derive instead of reusing 3c-D's `regularizedInvSub`
version: downstream (Chip 3c-F-3e) we need the `radialCutoff`-shaped
factor specifically, because Chip 3c-F-2-final's universal constant
`∫ ∂̄(radialBump 0 1)(w)/w = -π` only applies to that bump.

## Main result

* `balance_iteratedIntegral_eq_zero_radial : ContDiff ℝ 1 α →
    tsupport α ⊆ Metric.ball 0 L → 0 < L →
    ∫x in -L..L, ∫y in -L..L,
      partialZBar α ((x:ℂ)+y*I) * regularizedInvSubRadial z ε ((x:ℂ)+y*I)
        + α ((x:ℂ)+y*I) *
            partialZBar (regularizedInvSubRadial z ε) ((x:ℂ)+y*I)
      = 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric MeasureTheory
open scoped Real Topology Interval

namespace JacobianChallenge.PompeiuKernel

/-- `α * regularizedInvSubRadial z ε` is `C¹` when `α` is `C¹`. -/
lemma contDiff_alpha_mul_regInvSubRadial
    {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fun η => α η * regularizedInvSubRadial z ε η) :=
  h_α.mul (regularizedInvSubRadial_contDiff z hε)

/-- The support of `α * regularizedInvSubRadial z ε` is contained in the
support of `α`. -/
lemma hasCompactSupport_alpha_mul_regInvSubRadial
    {α : ℂ → ℂ} (h_supp : HasCompactSupport α) (z : ℂ) (ε : ℝ) :
    HasCompactSupport (fun η => α η * regularizedInvSubRadial z ε η) :=
  h_supp.mul_right

/-- `tsupport (α * regularizedInvSubRadial z ε) ⊆ tsupport α`. -/
lemma tsupport_alpha_mul_regInvSubRadial_subset
    (α : ℂ → ℂ) (z : ℂ) (ε : ℝ) :
    tsupport (fun η => α η * regularizedInvSubRadial z ε η) ⊆ tsupport α := by
  apply closure_mono
  intro η hη
  rw [Function.mem_support] at hη ⊢
  intro h_zero
  apply hη
  rw [h_zero, zero_mul]

/-- Pointwise Leibniz expansion. Uses the generic `partialZBar_mul`
from `Manifold/PartialZBar.lean`. -/
lemma partialZBar_alpha_mul_regInvSubRadial
    {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α) (z : ℂ) {ε : ℝ} (hε : 0 < ε) (ζ : ℂ) :
    partialZBar (fun η => α η * regularizedInvSubRadial z ε η) ζ
      = partialZBar α ζ * regularizedInvSubRadial z ε ζ
        + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ := by
  have h_α_diff : DifferentiableAt ℝ α ζ :=
    (h_α.differentiable (by norm_num)).differentiableAt
  have h_g_contDiff : ContDiff ℝ (1 : ℕ∞) (regularizedInvSubRadial z ε) :=
    regularizedInvSubRadial_contDiff z hε
  have h_g_diff : DifferentiableAt ℝ (regularizedInvSubRadial z ε) ζ :=
    (h_g_contDiff.differentiable (by norm_num)).differentiableAt
  have h_mul := partialZBar_mul h_α_diff h_g_diff
  show partialZBar ((α : ℂ → ℂ) * (regularizedInvSubRadial z ε)) ζ
        = partialZBar α ζ * regularizedInvSubRadial z ε ζ
          + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ
  exact h_mul

/-- **Chip 3c-F-3b — radial-cutoff Stokes balance.** For `α : ℂ → ℂ` of
class `C¹` with compact support whose `tsupport` is contained in
`Metric.ball 0 L`,

```
∫ x in -L..L, ∫ y in -L..L,
  partialZBar α (x+y*I) * regularizedInvSubRadial z ε (x+y*I)
    + α (x+y*I) * partialZBar (regularizedInvSubRadial z ε) (x+y*I) = 0.
```

Identical proof shape to Chip 3c-D's `balance_iteratedIntegral_eq_zero`,
but with `regularizedInvSubRadial` in place of `regularizedInvSub`. -/
theorem balance_iteratedIntegral_eq_zero_radial
    {α : ℂ → ℂ} (h_α : ContDiff ℝ 1 α)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    {L : ℝ} (hL_pos : 0 < L)
    (hL_supp : tsupport α ⊆ Metric.ball 0 L) :
    ∫ x in -L..L, ∫ y in -L..L,
      partialZBar α ((x : ℂ) + y * I) * regularizedInvSubRadial z ε ((x : ℂ) + y * I)
        + α ((x : ℂ) + y * I)
            * partialZBar (regularizedInvSubRadial z ε) ((x : ℂ) + y * I)
      = 0 := by
  set f : ℂ → ℂ := fun η => α η * regularizedInvSubRadial z ε η with hf_def
  have h_f_smooth : ContDiff ℝ 1 f := contDiff_alpha_mul_regInvSubRadial h_α z hε
  have h_f_supp : tsupport f ⊆ Metric.ball 0 L :=
    (tsupport_alpha_mul_regInvSubRadial_subset α z ε).trans hL_supp
  have h_stokes := iteratedIntegral_partialZBar_eq_zero h_f_smooth hL_pos h_f_supp
  have h_pointwise : ∀ ζ : ℂ,
      partialZBar f ζ
        = partialZBar α ζ * regularizedInvSubRadial z ε ζ
          + α ζ * partialZBar (regularizedInvSubRadial z ε) ζ :=
    fun ζ => partialZBar_alpha_mul_regInvSubRadial h_α z hε ζ
  have h_rewrite :
      (∫ x in -L..L, ∫ y in -L..L, partialZBar f ((x : ℂ) + y * I))
        = ∫ x in -L..L, ∫ y in -L..L,
            partialZBar α ((x : ℂ) + y * I) * regularizedInvSubRadial z ε ((x : ℂ) + y * I)
              + α ((x : ℂ) + y * I)
                  * partialZBar (regularizedInvSubRadial z ε) ((x : ℂ) + y * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply intervalIntegral.integral_congr
    intro y _
    exact h_pointwise ((x : ℂ) + y * I)
  rw [h_rewrite] at h_stokes
  exact h_stokes

end JacobianChallenge.PompeiuKernel
