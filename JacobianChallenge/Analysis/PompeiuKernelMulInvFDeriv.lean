/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-B: `HasFDerivAt` for `α(η)·(η-z)⁻¹` off the singularity

This file upgrades Chip 3c-A's pointwise `partialZBar` identity to a
`HasFDerivAt` statement at each `ζ ≠ z`. This is the **input shape**
required by mathlib's rectangle Stokes lemma
`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`
([`Mathlib/Analysis/Complex/CauchyIntegral.lean:187`](.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean)),
whose hypothesis `Hd : ∀ x ∈ interior \ s, HasFDerivAt f (f' x) x`
needs an explicit `ℝ`-Fréchet derivative pointwise off the bad set
`s` (here `s = {z}`, the lone singularity of `(η - z)⁻¹`).

## Chip 3 arc context

* Chip 3a — small-disc limit `∮_{C(z,ε)} α(ζ)·(ζ-z)⁻¹ dζ → 2πI · α(z)`.
* Chip 3b — algebraic bridge `partialZBar (pompeiuKernel α) = pompeiuKernel (partialZBar α)`.
* Chip 3c-A (`PompeiuKernelLeibniz.lean`) — pointwise `partialZBar` reduction off `z`.
* **Chip 3c-B (this file)** — `HasFDerivAt` for the rectangle integrand off `z`.
* Chip 3c-C (next) — rectangle Stokes invocation with `s = {z}` as the
  countable bad set.

## Main results

* `hasDerivAt_inv_sub_const` — `HasDerivAt (fun η => (η - z)⁻¹) (-(ζ-z)⁻²) ζ`
  over `ℂ` at `ζ ≠ z`. Composition of `hasDerivAt_inv` with `sub_const`.
* `hasFDerivAt_real_inv_sub_const` — the `ℝ`-Fréchet form, with explicit
  fderiv `((smulRight 1 (-(ζ-z)⁻²)) : ℂ →L[ℂ] ℂ).restrictScalars ℝ`.
* `hasFDerivAt_mul_inv_sub` — the product-rule combination
  `HasFDerivAt (fun η => α η * (η - z)⁻¹) (α' ζ-side + α ζ • g'_ζ) ζ`
  for any `α` real-differentiable at `ζ`.

Both `hasFDerivAt_real_inv_sub_const` and `hasFDerivAt_mul_inv_sub` use
`set_option backward.isDefEq.respectTransparency false in` to dodge the
`IsScalarTower ℝ ℂ ℂ` synthesis diamond — the same workaround mathlib
uses in `HasDerivAt.real_of_complex` (`Analysis/Complex/RealDeriv.lean:44`)
and that Chip 3c-A used.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

variable {α : ℂ → ℂ} {z ζ : ℂ}

/-! ## `HasDerivAt` and `HasFDerivAt` for `(η - z)⁻¹` -/

/-- `HasDerivAt (fun η => (η - z)⁻¹) (-(ζ - z)⁻²) ζ` over `ℂ` at any
`ζ ≠ z`. Composition `inv ∘ (· - z)` with chain rule
`HasDerivAt.comp`. -/
lemma hasDerivAt_inv_sub_const (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    HasDerivAt (fun η : ℂ => (η - z)⁻¹) (-((ζ - z) ^ 2)⁻¹) ζ := by
  have h_sub : HasDerivAt (fun η : ℂ => η - z) 1 ζ :=
    (hasDerivAt_id ζ).sub_const z
  have h_ne : (fun η : ℂ => η - z) ζ ≠ 0 := sub_ne_zero.mpr hζ
  have h_comp := (hasDerivAt_inv h_ne).comp ζ h_sub
  -- h_comp : HasDerivAt (((·)⁻¹) ∘ (fun η => η - z)) (-((ζ - z)^2)⁻¹ * 1) ζ
  simpa using h_comp

set_option backward.isDefEq.respectTransparency false in
/-- The `ℝ`-Fréchet form of `hasDerivAt_inv_sub_const`. The explicit
fderiv is multiplication by `-((ζ - z) ^ 2)⁻¹`, packaged as a
`ℂ →L[ℝ] ℂ` via `restrictScalars`. -/
lemma hasFDerivAt_real_inv_sub_const (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    HasFDerivAt (fun η : ℂ => (η - z)⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((ζ - z) ^ 2)⁻¹))
        : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
      ζ :=
  (hasDerivAt_inv_sub_const z hζ).hasFDerivAt.restrictScalars ℝ

/-! ## `HasFDerivAt` for the Pompeiu integrand off the singularity -/

set_option backward.isDefEq.respectTransparency false in
/-- **`HasFDerivAt` for the Pompeiu integrand off `z` (Chip 3c-B).**
For `α : ℂ → ℂ` real-differentiable at `ζ` and any `z` with `ζ ≠ z`,
the function `fun η => α η * (η - z)⁻¹` is `ℝ`-Fréchet-differentiable
at `ζ` with explicit fderiv given by the product rule.

This is the input shape for mathlib's rectangle Stokes
(`Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`),
whose `Hd` hypothesis requires `HasFDerivAt f (f' x) x` pointwise off
a countable bad set. Here that set is `{z}`. -/
theorem hasFDerivAt_mul_inv_sub
    (h_α : HasFDerivAt α (fderiv ℝ α ζ) ζ) (z : ℂ) (hζ : ζ ≠ z) :
    HasFDerivAt (fun η : ℂ => α η * (η - z)⁻¹)
      (α ζ •
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((ζ - z) ^ 2)⁻¹))
              : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
        + (ζ - z)⁻¹ • fderiv ℝ α ζ)
      ζ := by
  have h_inv := hasFDerivAt_real_inv_sub_const z hζ
  -- `HasFDerivAt.mul` on `α * (·-z)⁻¹` gives fderiv `α ζ • g' + (ζ-z)⁻¹ • α'`.
  have h_mul := h_α.mul h_inv
  -- The function from `HasFDerivAt.mul` is `α * (fun η => (η - z)⁻¹)` (Pi.mul),
  -- which is definitionally equal to `fun η => α η * (η - z)⁻¹`.
  exact h_mul

/-- Convenient corollary: same statement for `α ∈ ContDiff ℝ 1`, with
`HasFDerivAt α (fderiv ℝ α ζ) ζ` extracted automatically from
differentiability. -/
theorem hasFDerivAt_mul_inv_sub_of_contDiff
    (h_smooth : ContDiff ℝ 1 α) (z : ℂ) (hζ : ζ ≠ z) :
    HasFDerivAt (fun η : ℂ => α η * (η - z)⁻¹)
      (α ζ •
          (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-((ζ - z) ^ 2)⁻¹))
              : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
        + (ζ - z)⁻¹ • fderiv ℝ α ζ)
      ζ := by
  have h_diff : Differentiable ℝ α :=
    h_smooth.differentiable (by norm_num)
  exact hasFDerivAt_mul_inv_sub h_diff.differentiableAt.hasFDerivAt z hζ

end JacobianChallenge.PompeiuKernel
