/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBar
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Holomorphic chain rule for `partialZBar`

For `Φ : ℂ → ℂ` complex-differentiable at `z` and `f : ℂ → ℂ`
real-differentiable at `Φ z`, the antiholomorphic derivative satisfies

    `partialZBar (f ∘ Φ) z = partialZBar f (Φ z) * conj (deriv Φ z)`.

This is the `(0,1)`-form transformation law: under a holomorphic chart
change, the chart-local `∂̄` picks up a conjugate-derivative factor.
Specializing `f` to a chart-local representative `u ∘ c.symm` and `Φ`
to a chart transition makes `partialZBarChart` a chart-pullback whose
sections obey the `(0,1)`-form gluing rule on a complex 1-manifold.

This file is still chart-free (works entirely on `ℂ → ℂ`); the
chart-local definition and the manifold-wide `(0,1)`-form bundle are in
later files.

## Main result

* `partialZBar_comp_of_differentiableAt`:
  `partialZBar (f ∘ Φ) z = partialZBar f (Φ z) * conj (deriv Φ z)`
  when `Φ` is complex-differentiable at `z` and `f` is real-differentiable
  at `Φ z`. -/

namespace JacobianChallenge

open Complex

/-- Local copy of the `IsScalarTower ℝ ℂ ℂ` workaround used by
`PartialZBar.lean` (same comment applies — see file docstring of
`Manifold/MFDerivComplexToRealApply.lean`). Both helpers are private,
declared per-file to avoid leaking the workaround into the public API. -/
@[reducible] private def isScalarTower_R_C_C : IsScalarTower ℝ ℂ ℂ :=
  ⟨fun (r : ℝ) (c c' : ℂ) => by
    show (r • c) • c' = r • c • c'
    rw [smul_assoc]⟩

/-- Wrapper for `DifferentiableAt.restrictScalars ℝ` with explicit
`IsScalarTower ℝ ℂ ℂ` instance. -/
private theorem differentiableAt_restrictScalars_R_C_C
    {f : ℂ → ℂ} {x : ℂ} (h : DifferentiableAt ℂ f x) :
    DifferentiableAt ℝ f x :=
  @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C
    ℂ _ _ _ isScalarTower_R_C_C _ _ h

/-- Wrapper for `HasFDerivAt.restrictScalars ℝ` with explicit
`IsScalarTower ℝ ℂ ℂ` instance, following the pattern in
`MFDerivComplexToRealApply.lean`. -/
private theorem hasFDerivAt_restrictScalars_R_C_C
    {f : ℂ → ℂ} {f' : ℂ →L[ℂ] ℂ} {x : ℂ} (h : HasFDerivAt f f' x) :
    HasFDerivAt f
      (@ContinuousLinearMap.restrictScalars ℂ ℂ ℂ ℝ _ _ _ _ _ _ _ _ _ _ _ f') x :=
  @HasFDerivAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ isScalarTower_R_C_C
    ℂ _ _ _ isScalarTower_R_C_C _ _ _ h

/-- Decomposition of an `ℝ`-linear continuous map `ℂ →L[ℝ] ℂ` into its
action on `1` and `I`. By real-and-imaginary parts of the input, every
`v : ℂ` is the `ℝ`-linear combination `v.re • 1 + v.im • I`. -/
private lemma ContinuousLinearMap_R_to_C_decompose
    (T : ℂ →L[ℝ] ℂ) (v : ℂ) :
    T v = (v.re : ℂ) * T 1 + (v.im : ℂ) * T I := by
  -- Split the computation into the two summands of `v = ↑v.re + ↑v.im * I`.
  -- `Complex.real_smul` says `(r : ℝ) • (z : ℂ) = ↑r * z` (it's `rfl`),
  -- so `T.map_smul` (over ℝ) gives the equations we need; `mul_one` cleans
  -- the residual `* 1` in the `re` case.
  have h_re : T ((v.re : ℂ)) = (v.re : ℂ) * T 1 := by
    have hms : T ((v.re : ℂ) * 1) = (v.re : ℂ) * T 1 :=
      T.map_smul (v.re : ℝ) (1 : ℂ)
    rwa [mul_one] at hms
  have h_im : T ((v.im : ℂ) * I) = (v.im : ℂ) * T I :=
    T.map_smul (v.im : ℝ) (I : ℂ)
  conv_lhs => rw [← Complex.re_add_im v, map_add, h_re, h_im]

/-- `(fderiv ℝ Φ z) v = (deriv Φ z) * v` when `Φ` is complex-differentiable
at `z`. The real-linear `fderiv ℝ Φ z` is the `restrictScalars ℝ` of the
complex-linear `fderiv ℂ Φ z`, which is itself multiplication by the
complex derivative. -/
private lemma fderiv_R_apply_of_differentiableAt_complex
    {Φ : ℂ → ℂ} {z : ℂ} (hΦ : DifferentiableAt ℂ Φ z) (v : ℂ) :
    (fderiv ℝ Φ z) v = (deriv Φ z) * v := by
  -- Build a ℂ-linear `f'` via the complex derivative, restrict to ℝ.
  have hf_C : HasFDerivAt Φ (fderiv ℂ Φ z) z := hΦ.hasFDerivAt
  have hf_R : HasFDerivAt Φ
      (@ContinuousLinearMap.restrictScalars ℂ ℂ ℂ ℝ _ _ _ _ _ _ _ _ _ _ _
        (fderiv ℂ Φ z)) z :=
    hasFDerivAt_restrictScalars_R_C_C hf_C
  rw [hf_R.fderiv]
  -- The restricted CLM applied to `v` is `(fderiv ℂ Φ z) v` as a value.
  show (fderiv ℂ Φ z) v = deriv Φ z * v
  rw [fderiv_eq_smul_deriv, smul_eq_mul, mul_comm]

/-- **Holomorphic chain rule for `∂̄`:**
For `Φ` complex-differentiable at `z` and `f` real-differentiable at
`Φ z`,
    `partialZBar (f ∘ Φ) z = partialZBar f (Φ z) * conj (deriv Φ z)`.

This identity is what makes `∂̄` transform as a `(0,1)`-form under
holomorphic chart changes: pulled back through a holomorphic transition
`Φ`, the chart-local `∂̄ u` picks up a factor of `conj(Φ')`. -/
lemma partialZBar_comp_of_differentiableAt
    {f Φ : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (Φ z)) (hΦ : DifferentiableAt ℂ Φ z) :
    partialZBar (f ∘ Φ) z
      = partialZBar f (Φ z) * (starRingEnd ℂ) (deriv Φ z) := by
  have hΦR : DifferentiableAt ℝ Φ z := differentiableAt_restrictScalars_R_C_C hΦ
  -- Real chain rule.
  have hcomp : fderiv ℝ (f ∘ Φ) z
      = (fderiv ℝ f (Φ z)).comp (fderiv ℝ Φ z) :=
    fderiv_comp z hf hΦR
  -- Set abbreviations to keep the algebra readable.
  set D : ℂ := deriv Φ z with hD_def
  set α : ℂ := (fderiv ℝ f (Φ z)) 1 with hα_def
  set β : ℂ := (fderiv ℝ f (Φ z)) I with hβ_def
  -- (fderiv ℝ (f∘Φ) z) 1 = (fderiv ℝ f (Φ z)) ((fderiv ℝ Φ z) 1)
  --                     = (fderiv ℝ f (Φ z)) (D * 1)
  --                     = (fderiv ℝ f (Φ z)) D
  --                     = D.re * α + D.im * β    [by R-linearity decomp]
  have h1 : (fderiv ℝ (f ∘ Φ) z) 1 = (D.re : ℂ) * α + (D.im : ℂ) * β := by
    rw [hcomp, ContinuousLinearMap.comp_apply, fderiv_R_apply_of_differentiableAt_complex hΦ,
        mul_one]
    exact ContinuousLinearMap_R_to_C_decompose (fderiv ℝ f (Φ z)) D
  -- (fderiv ℝ (f∘Φ) z) I = (fderiv ℝ f (Φ z)) (D * I)
  --                    = (D * I).re * α + (D * I).im * β
  --                    = -D.im * α + D.re * β
  have h_DI_re : (D * I).re = -D.im := by simp [Complex.mul_re]
  have h_DI_im : (D * I).im = D.re := by simp [Complex.mul_im]
  have hI : (fderiv ℝ (f ∘ Φ) z) I = -(D.im : ℂ) * α + (D.re : ℂ) * β := by
    rw [hcomp, ContinuousLinearMap.comp_apply, fderiv_R_apply_of_differentiableAt_complex hΦ]
    have hdecomp := ContinuousLinearMap_R_to_C_decompose (fderiv ℝ f (Φ z)) (D * I)
    rw [h_DI_re, h_DI_im] at hdecomp
    -- hdecomp : T (D * I) = (↑(-D.im) : ℂ) * α + (↑D.re : ℂ) * β
    -- Goal   : T (D * I)  = -(↑D.im : ℂ) * α + (↑D.re : ℂ) * β
    rw [hdecomp]
    push_cast
    ring
  -- partialZBar (f ∘ Φ) z = ½ (h1 + I * hI)
  -- partialZBar f (Φ z) * conj D = ½ (α + I*β) * (D.re - I*D.im)
  -- Match coefficients via `ring` after expanding conj.
  have h_conj : (starRingEnd ℂ) D = (D.re : ℂ) - (D.im : ℂ) * I := by
    apply Complex.ext <;> simp
  show partialZBar (f ∘ Φ) z = partialZBar f (Φ z) * (starRingEnd ℂ) D
  unfold partialZBar
  rw [h1, hI, h_conj]
  -- LHS: (2:ℂ)⁻¹ * ((D.re * α + D.im * β) + I * (-D.im * α + D.re * β))
  -- RHS: ((2:ℂ)⁻¹ * (α + I * β)) * (D.re - D.im * I)
  show (2 : ℂ)⁻¹ * (((D.re : ℂ) * α + (D.im : ℂ) * β)
                  + I * (-(D.im : ℂ) * α + (D.re : ℂ) * β))
      = (2 : ℂ)⁻¹ * (α + I * β) * ((D.re : ℂ) - (D.im : ℂ) * I)
  have hI_sq : I * I = (-1 : ℂ) := Complex.I_mul_I
  -- Open up and use I*I = -1
  ring_nf
  rw [show I^2 = (-1 : ℂ) from Complex.I_sq]
  ring

end JacobianChallenge
