/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JacobianChallenge.Analysis.PompeiuKernelRadialBump
import JacobianChallenge.Manifold.PartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Cauchy-Pompeiu kernel — Chip 3c-F (Section B): radial Wirtinger formula

For a radially-symmetric function `f(w) = ψ(‖w - z‖)` on `ℂ` with
`η ≠ z` and `ψ` differentiable at `‖η - z‖`,
```
(∂̄ f)(η) = (1/2) · ψ'(‖η - z‖) / ‖η - z‖ · (η - z).
```

The derivation uses `Complex.re_add_im` to assemble `(η - z) =
((η - z).re : ℂ) + I · ((η - z).im : ℂ)` from the two partial-derivative
components.

## Main results

* `hasFDerivAt_norm_sq_sub_const`: derivative of `fun w => ‖w - z‖²`.
* `hasFDerivAt_norm_sub_const_of_ne`: derivative of `fun w => ‖w - z‖`
  at `η ≠ z`, via the `sqrt` chain rule.
* `partialZBar_radial_of_ne`: the headline Wirtinger formula.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex Filter Set Topology Metric Real
open scoped Topology

namespace JacobianChallenge.PompeiuKernel

open JacobianChallenge

/-! ## Step 1: `fderiv (fun w => ‖w - z‖²)` -/

/-- `fderiv ℝ (fun w => ‖w - z‖²) η = 2 • innerSL ℝ (η - z)`, by chain
rule on `‖·‖²` (mathlib's `fderiv_norm_sq_apply`) composed with
`w ↦ w - z`. -/
lemma hasFDerivAt_norm_sq_sub_const (z η : ℂ) :
    HasFDerivAt (fun w : ℂ => ‖w - z‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ)) η := by
  have h_sub : HasFDerivAt (fun w : ℂ => w - z) (ContinuousLinearMap.id ℝ ℂ) η :=
    (hasFDerivAt_id η).sub_const z
  have h_sq : HasFDerivAt (fun x : ℂ => ‖x‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ)) (η - z) :=
    (hasStrictFDerivAt_norm_sq (η - z)).hasFDerivAt
  have h_comp := h_sq.comp η h_sub
  -- After composition, the derivative is `(2 • innerSL) ∘ id = 2 • innerSL`.
  simpa using h_comp

/-! ## Step 2: `fderiv (fun w => ‖w - z‖)` at `η ≠ z` -/

/-- For `η ≠ z`, `fderiv ℝ (fun w => ‖w - z‖) η = (1/‖η-z‖) • innerSL ℝ (η - z)`. -/
lemma hasFDerivAt_norm_sub_const_of_ne {z η : ℂ} (hη : η ≠ z) :
    HasFDerivAt (fun w : ℂ => ‖w - z‖)
      ((1 / ‖η - z‖) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ)) η := by
  have h_sub_ne : η - z ≠ 0 := sub_ne_zero.mpr hη
  have h_norm_ne : ‖η - z‖ ≠ 0 := norm_ne_zero_iff.mpr h_sub_ne
  have h_sq_ne : ‖η - z‖ ^ 2 ≠ 0 := pow_ne_zero 2 h_norm_ne
  have h_sq := hasFDerivAt_norm_sq_sub_const z η
  -- `HasFDerivAt.sqrt` gives `fderiv` of `√(f w)` from `fderiv` of `f w`.
  have h_sqrt := h_sq.sqrt h_sq_ne
  -- `h_sqrt : HasFDerivAt (fun w => √(‖w - z‖²))
  --     ((1/(2·√(‖η-z‖²))) • (2 • innerSL ℝ (η - z))) η`.
  -- Rewrite the function side via √(‖·‖²) = ‖·‖.
  have h_fn_eq : (fun w : ℂ => Real.sqrt (‖w - z‖ ^ 2)) = (fun w : ℂ => ‖w - z‖) := by
    funext w; exact Real.sqrt_sq (norm_nonneg _)
  rw [h_fn_eq] at h_sqrt
  -- Rewrite the derivative side: √(‖η-z‖²) = ‖η-z‖.
  have h_sqrt_norm_sq : Real.sqrt (‖η - z‖ ^ 2) = ‖η - z‖ :=
    Real.sqrt_sq (norm_nonneg _)
  rw [h_sqrt_norm_sq] at h_sqrt
  -- The scalar `1/(2‖η-z‖) • (2 • inner) = 1/‖η-z‖ • inner`.
  have h_scalar :
      ((1 / (2 * ‖η - z‖)) • ((2 : ℕ) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ)))
        = ((1 / ‖η - z‖) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ)) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ (2 : ℕ), smul_smul]
    congr 1
    push_cast
    field_simp
  rw [h_scalar] at h_sqrt
  exact h_sqrt

/-! ## Step 3: evaluate the inner-product CLM at `1` and `I` -/

/-- `(innerSL ℝ w) 1 = w.re` for `w : ℂ`. -/
lemma innerSL_one_complex (w : ℂ) :
    (innerSL ℝ w : ℂ →L[ℝ] ℝ) (1 : ℂ) = w.re := by
  show @inner ℝ ℂ _ w 1 = w.re
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
        Complex.conj_re, Complex.conj_im]

/-- `(innerSL ℝ w) I = w.im` for `w : ℂ`. -/
lemma innerSL_I_complex (w : ℂ) :
    (innerSL ℝ w : ℂ →L[ℝ] ℝ) (I : ℂ) = w.im := by
  show @inner ℝ ℂ _ w I = w.im
  rw [Complex.inner]
  -- (I * conj w).re = (I * ⟨w.re, -w.im⟩).re
  -- = (⟨0,1⟩ * ⟨w.re, -w.im⟩).re = (0·w.re - 1·(-w.im)) = w.im.
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im]

/-! ## Step 4: the radial Wirtinger formula -/

/-- **Radial Wirtinger formula (Chip 3c-F Section B).** For `η ≠ z` and
`ψ : ℝ → ℝ` differentiable at `‖η - z‖` with derivative `ψ'`,
```
partialZBar (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ)) η
  = ((ψ' / 2 : ℝ) : ℂ) * (η - z) / ‖η - z‖.
```

This is the structural identity at the heart of the universal-constant
calculation `∫∫ (∂̄ φ_1)(w)/w dA = -π` (Chip 3c-F Section C). -/
theorem partialZBar_radial_of_ne
    {z η : ℂ} (hη : η ≠ z) {ψ : ℝ → ℝ} {ψ' : ℝ}
    (hψ : HasDerivAt ψ ψ' ‖η - z‖) :
    partialZBar (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ)) η
      = ((ψ' / 2 : ℝ) : ℂ) * (η - z) / ‖η - z‖ := by
  have h_sub_ne : η - z ≠ 0 := sub_ne_zero.mpr hη
  have h_norm_ne : ‖η - z‖ ≠ 0 := norm_ne_zero_iff.mpr h_sub_ne
  -- Step A: `fderiv` of the norm at η (ℂ → ℝ).
  have h_norm := hasFDerivAt_norm_sub_const_of_ne hη (z := z)
  -- Step B: compose with ψ.
  have h_ψ_norm : HasFDerivAt (fun w : ℂ => ψ ‖w - z‖)
      (ψ' • ((1 / ‖η - z‖) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ))) η :=
    hψ.comp_hasFDerivAt η h_norm
  -- Step C: lift to ℂ via `Complex.ofRealCLM`.
  have h_lift : HasFDerivAt (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ))
      (Complex.ofRealCLM.comp
        (ψ' • ((1 / ‖η - z‖) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ)))) η :=
    Complex.ofRealCLM.hasFDerivAt.comp η h_ψ_norm
  -- Step D: evaluate the lifted fderiv at v = 1 and v = I.
  have h_fd_at_1 :
      (fderiv ℝ (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ)) η) 1
        = ((ψ' * (η - z).re / ‖η - z‖ : ℝ) : ℂ) := by
    rw [h_lift.fderiv]
    show Complex.ofRealCLM
        ((ψ' • ((1 / ‖η - z‖) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ))) (1 : ℂ))
      = _
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
               innerSL_one_complex, Complex.ofRealCLM_apply]
    push_cast
    ring
  have h_fd_at_I :
      (fderiv ℝ (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ)) η) I
        = ((ψ' * (η - z).im / ‖η - z‖ : ℝ) : ℂ) := by
    rw [h_lift.fderiv]
    show Complex.ofRealCLM
        ((ψ' • ((1 / ‖η - z‖) • (innerSL ℝ (η - z) : ℂ →L[ℝ] ℝ))) (I : ℂ))
      = _
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
               innerSL_I_complex, Complex.ofRealCLM_apply]
    push_cast
    ring
  -- Step E: assemble the `partialZBar` definition.
  show (2 : ℂ)⁻¹ *
        ((fderiv ℝ (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ)) η) 1
          + I * (fderiv ℝ (fun w : ℂ => ((ψ ‖w - z‖ : ℝ) : ℂ)) η) I)
        = ((ψ' / 2 : ℝ) : ℂ) * (η - z) / ‖η - z‖
  rw [h_fd_at_1, h_fd_at_I]
  -- Push casts, then factor and apply `Complex.re_add_im` algebraically.
  have h_re_add_im : ((η - z).re : ℂ) + I * ((η - z).im : ℂ) = η - z := by
    have := Complex.re_add_im (η - z)
    linear_combination this
  push_cast
  -- Goal: (2:ℂ)⁻¹ * (ψ' * (η-z).re / ‖η-z‖ + I * (ψ' * (η-z).im / ‖η-z‖))
  --      = (ψ' / 2) * (η - z) / ‖η - z‖
  -- Factor: LHS = (ψ' / 2) / ‖η - z‖ * ((η-z).re + I * (η-z).im) = RHS via re_add_im.
  have h_factor : (2 : ℂ)⁻¹ * (↑ψ' * ↑(η - z).re / ↑‖η - z‖
        + I * (↑ψ' * ↑(η - z).im / ↑‖η - z‖))
      = (↑ψ' / 2) / ↑‖η - z‖ * (↑(η - z).re + I * ↑(η - z).im) := by
    ring
  rw [h_factor, h_re_add_im]
  ring

end JacobianChallenge.PompeiuKernel

end
