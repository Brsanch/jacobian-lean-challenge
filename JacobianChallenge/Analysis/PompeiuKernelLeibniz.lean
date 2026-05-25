/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import JacobianChallenge.Manifold.PartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Cauchy-Pompeiu kernel — Chip 3c-A: Leibniz reduction for `α(η) · (η - z)⁻¹`

This file proves the pointwise Leibniz identity

```
partialZBar (fun η => α η * (η - z)⁻¹) ζ = partialZBar α ζ * (ζ - z)⁻¹
```

for `α : ℂ → ℂ` real-differentiable at `ζ` and any `z` with `ζ ≠ z`.
This is the algebraic core of the Cauchy-Pompeiu rectangle integrand
reduction (Chip 3c): on the off-singularity locus `ζ ≠ z`, the
antiholomorphic derivative of the Pompeiu integrand reduces to
`(∂̄α)(ζ) · (ζ - z)⁻¹` because the singular factor `(η - z)⁻¹` is
`ℂ`-holomorphic at `η = ζ` (Cauchy-Riemann).

## Chip 3 arc context

* Chip 3a (`PompeiuKernelSmallDiscLimit.lean`) — small-disc limit
  `∮_{C(z,ε)} α(ζ)·(ζ-z)⁻¹ dζ → 2πI · α(z)`.
* Chip 3b (`PompeiuKernelPartialZBarBridge.lean`) — algebraic bridge
  `partialZBar (pompeiuKernel α) = pompeiuKernel (partialZBar α)`.
* **Chip 3c-A (this file)** — Leibniz reduction for the rectangle
  integrand: on `ζ ≠ z`, `∂̄(α · (·-z)⁻¹)(ζ) = (∂̄α)(ζ) · (ζ-z)⁻¹`.
* Chip 3c-B (next) — rectangle Stokes for `α(·)·(·-z)⁻¹` on
  `[−L, L]² \ ball z ε` using mathlib's rectangle Stokes plus a smooth
  cutoff to handle the inner hole.
* Chip 3c-C — DCT limit `ε → 0`, combining with Chip 3a's small-disc
  limit, to conclude `pompeiuKernel (partialZBar α) z = α z`.

## Main results

* `differentiableAt_inv_sub_const` — `DifferentiableAt ℂ (fun η => (η - z)⁻¹) ζ`
  whenever `ζ ≠ z`.
* `partialZBar_inv_sub_const_eq_zero` — `partialZBar (fun η => (η - z)⁻¹) ζ = 0`
  for `ζ ≠ z` (via Cauchy-Riemann on the holomorphic factor).
* `partialZBar_mul_inv_sub` — the main Leibniz identity.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

variable {α : ℂ → ℂ} {z ζ : ℂ}

/-! ## `ℂ`-differentiability and `partialZBar` of `(η - z)⁻¹` off the singularity -/

/-- The singular factor `(η - z)⁻¹` is `ℂ`-differentiable at `ζ` whenever
`ζ ≠ z`. The function decomposes as `inv ∘ (· - z)`, with `(· - z)` an
affine map and `inv` differentiable away from `0`. -/
lemma differentiableAt_inv_sub_const (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    DifferentiableAt ℂ (fun η : ℂ => (η - z)⁻¹) ζ := by
  have h_sub : DifferentiableAt ℂ (fun η : ℂ => η - z) ζ :=
    (differentiableAt_id).sub_const z
  have h_ne : (fun η : ℂ => η - z) ζ ≠ 0 := sub_ne_zero.mpr hζ
  exact (differentiableAt_inv_iff.mpr h_ne).comp ζ h_sub

set_option backward.isDefEq.respectTransparency false in
/-- The singular factor `(η - z)⁻¹` is `ℝ`-differentiable at `ζ` whenever
`ζ ≠ z` (it is in fact `ℂ`-differentiable, hence `ℝ`-differentiable by
`DifferentiableAt.restrictScalars`). Needed for `partialZBar_mul`.

The `set_option backward.isDefEq.respectTransparency false in` annotation
mirrors mathlib's `HasDerivAt.real_of_complex`
(`Mathlib/Analysis/Complex/RealDeriv.lean:44`) and dodges the
`IsScalarTower ℝ ℂ ℂ` instance-synthesis diamond. -/
lemma differentiableAt_real_inv_sub_const (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    DifferentiableAt ℝ (fun η : ℂ => (η - z)⁻¹) ζ :=
  (differentiableAt_inv_sub_const z hζ).restrictScalars ℝ

/-- `partialZBar (fun η => (η - z)⁻¹) ζ = 0` for `ζ ≠ z`: a
`ℂ`-differentiable function has vanishing antiholomorphic derivative
(Cauchy-Riemann). -/
lemma partialZBar_inv_sub_const_eq_zero (z : ℂ) {ζ : ℂ} (hζ : ζ ≠ z) :
    partialZBar (fun η : ℂ => (η - z)⁻¹) ζ = 0 :=
  partialZBar_eq_zero_of_differentiableAt (differentiableAt_inv_sub_const z hζ)

/-! ## The Leibniz reduction -/

/-- **Leibniz reduction (Chip 3c-A).** For `α : ℂ → ℂ` real-differentiable
at `ζ` and any `z` with `ζ ≠ z`,

```
partialZBar (fun η => α η * (η - z)⁻¹) ζ = partialZBar α ζ * (ζ - z)⁻¹.
```

The proof applies `partialZBar_mul` to `f := α` and `g := (· - z)⁻¹`; the
second term `α ζ · partialZBar g ζ` drops out because `g` is
`ℂ`-holomorphic at `ζ ≠ z` (`partialZBar_inv_sub_const_eq_zero`). -/
theorem partialZBar_mul_inv_sub
    (h_diff : DifferentiableAt ℝ α ζ) (z : ℂ) (hζ : ζ ≠ z) :
    partialZBar (fun η : ℂ => α η * (η - z)⁻¹) ζ
      = partialZBar α ζ * (ζ - z)⁻¹ := by
  -- Recast as `partialZBar (α * g) ζ` with `g η := (η - z)⁻¹`.
  set g : ℂ → ℂ := fun η => (η - z)⁻¹ with hg_def
  have h_eq : (fun η : ℂ => α η * (η - z)⁻¹) = α * g := by
    funext η; rfl
  have h_g_diff : DifferentiableAt ℝ g ζ := differentiableAt_real_inv_sub_const z hζ
  have h_g_pzb : partialZBar g ζ = 0 := partialZBar_inv_sub_const_eq_zero z hζ
  rw [h_eq, partialZBar_mul h_diff h_g_diff, h_g_pzb, mul_zero, add_zero]

end JacobianChallenge.PompeiuKernel
