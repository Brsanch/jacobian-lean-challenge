/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DBarOperator
import Mathlib.Analysis.Complex.RealDeriv

set_option linter.unusedSectionVars false

/-! # Chain rule for `dbarChart` with holomorphic inner function

If `g : ℂ → ℂ` is `ℂ`-differentiable at `z₀` with derivative `g'`, and
`f : ℂ → ℂ` is real-differentiable at `g(z₀)`, then

  `dbarChart (f ∘ g) z₀ = conj g' * dbarChart f (g z₀)`.

This is the Wirtinger-derivative chain rule restricted to the `∂̄` slot
when the inner function is holomorphic. Equivalently, holomorphic
substitution intertwines `∂̄` with multiplication by the complex
conjugate of the holomorphic derivative.

Geometric consequence on a complex 1-manifold (where chart transitions
are holomorphic): the *vanishing* `dbarChart … = 0` is invariant under
chart change. Concretely, if `g` is the transition map between two
charts and `g'(z₀) ≠ 0` (which holds for any chart transition of a
complex 1-manifold), then

  `dbarChart (f ∘ g) z₀ = 0 ↔ dbarChart f (g z₀) = 0`.

This is the **chart-independence of holomorphy** in the ∂̄ language.

No `sorry`, no `axiom`. -/

noncomputable section

open Complex

namespace JacobianChallenge

/-! ## Chain rule for `dbarChart` with holomorphic inner -/

/-- ℝ-linearity of `T : ℂ →L[ℝ] ℂ` applied to a real coefficient:
`T ((r : ℂ) * v) = (r : ℂ) * T v` for any real `r` and complex `v`. -/
private lemma fderivℝ_real_coef_mul
    (T : ℂ →L[ℝ] ℂ) (r : ℝ) (v : ℂ) :
    T ((r : ℂ) * v) = (r : ℂ) * T v := by
  have h1 : ((r : ℂ) * v) = r • v := (RCLike.real_smul_eq_coe_mul r v).symm
  have h2 : ((r : ℂ) * T v) = r • T v := (RCLike.real_smul_eq_coe_mul r (T v)).symm
  rw [h1, h2]
  exact T.map_smul r v

/-- `g' = g'.re + g'.im * I` over the complex numbers. -/
private lemma complex_eq_re_add_im (g' : ℂ) :
    g' = (g'.re : ℂ) + (g'.im : ℂ) * Complex.I := by
  exact (Complex.re_add_im g').symm

/-- `g' * I = -g'.im + g'.re * I`. -/
private lemma complex_mul_I_decomp (g' : ℂ) :
    g' * Complex.I = -(g'.im : ℂ) + (g'.re : ℂ) * Complex.I := by
  conv_lhs => rw [complex_eq_re_add_im g']
  have hI_sq : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination ((g'.im : ℂ)) * hI_sq

/-- **Chain rule for `dbarChart`** with a holomorphic inner function.

If `g` has a complex derivative `g'` at `z₀` and `f` is real-differentiable
at `g z₀`, then
`dbarChart (f ∘ g) z₀ = conj g' · dbarChart f (g z₀)`. -/
theorem dbarChart_comp_holomorphicInner {g f : ℂ → ℂ} {z₀ g' : ℂ}
    (hg : HasDerivAt g g' z₀)
    (hf : DifferentiableAt ℝ f (g z₀)) :
    dbarChart (f ∘ g) z₀
      = (starRingEnd ℂ) g' * dbarChart f (g z₀) := by
  -- Real Fréchet derivatives via mathlib's bridge.
  have hg_fd : HasFDerivAt g (g' • (1 : ℂ →L[ℝ] ℂ)) z₀ :=
    hg.complexToReal_fderiv
  have hf_fd : HasFDerivAt f (fderiv ℝ f (g z₀)) (g z₀) := hf.hasFDerivAt
  -- Chain rule on real Fréchet derivatives.
  have h_comp : HasFDerivAt (f ∘ g)
      ((fderiv ℝ f (g z₀)).comp (g' • (1 : ℂ →L[ℝ] ℂ))) z₀ :=
    hf_fd.comp z₀ hg_fd
  have h_fderiv_comp : fderiv ℝ (f ∘ g) z₀
      = (fderiv ℝ f (g z₀)).comp (g' • (1 : ℂ →L[ℝ] ℂ)) :=
    h_comp.fderiv
  unfold dbarChart
  rw [h_fderiv_comp]
  set T := fderiv ℝ f (g z₀)
  -- Reduce the composed evaluations.
  have hv1 : (T.comp (g' • (1 : ℂ →L[ℝ] ℂ))) 1 = T g' := by
    show T ((g' • (1 : ℂ →L[ℝ] ℂ)) 1) = T g'
    have : (g' • (1 : ℂ →L[ℝ] ℂ)) 1 = g' := by
      change g' * 1 = g'
      ring
    rw [this]
  have hvI : (T.comp (g' • (1 : ℂ →L[ℝ] ℂ))) Complex.I
      = T (g' * Complex.I) := by
    show T ((g' • (1 : ℂ →L[ℝ] ℂ)) Complex.I) = T (g' * Complex.I)
    have : (g' • (1 : ℂ →L[ℝ] ℂ)) Complex.I = g' * Complex.I := by
      change g' * Complex.I = g' * Complex.I
      rfl
    rw [this]
  rw [hv1, hvI]
  -- Expand T g' and T (g' * I) via ℝ-linearity.
  set a := g'.re
  set b := g'.im
  have hT_g' : T g' = (a : ℂ) * T 1 + (b : ℂ) * T Complex.I := by
    calc T g'
        = T ((a : ℂ) + (b : ℂ) * Complex.I) := by
          congr 1; exact complex_eq_re_add_im g'
      _ = T ((a : ℂ) * 1) + T ((b : ℂ) * Complex.I) := by
          rw [show ((a : ℂ) : ℂ) + (b : ℂ) * Complex.I
                  = (a : ℂ) * 1 + (b : ℂ) * Complex.I by ring]
          exact map_add _ _ _
      _ = (a : ℂ) * T 1 + (b : ℂ) * T Complex.I := by
          rw [fderivℝ_real_coef_mul T a 1, fderivℝ_real_coef_mul T b Complex.I]
  have hT_g'I : T (g' * Complex.I)
      = (-(b : ℂ)) * T 1 + (a : ℂ) * T Complex.I := by
    have h_neg_cast : -(b : ℂ) = ((-b : ℝ) : ℂ) := by push_cast; ring
    calc T (g' * Complex.I)
        = T (-(b : ℂ) + (a : ℂ) * Complex.I) := by
          congr 1; exact complex_mul_I_decomp g'
      _ = T (-(b : ℂ) * 1) + T ((a : ℂ) * Complex.I) := by
          rw [show -(b : ℂ) + (a : ℂ) * Complex.I
                  = -(b : ℂ) * 1 + (a : ℂ) * Complex.I by ring]
          exact map_add _ _ _
      _ = (-(b : ℂ)) * T 1 + (a : ℂ) * T Complex.I := by
          rw [h_neg_cast, fderivℝ_real_coef_mul T (-b) 1,
              fderivℝ_real_coef_mul T a Complex.I]
  -- conj g' = a - b·I.
  have h_conj : (starRingEnd ℂ) g' = (a : ℂ) - (b : ℂ) * Complex.I := by
    have he : g' = (a : ℂ) + (b : ℂ) * Complex.I := complex_eq_re_add_im g'
    rw [he]
    simp [Complex.conj_ofReal, Complex.conj_I, map_add, map_mul]
    ring
  -- Algebraic combination — uses `I² = -1` once.
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [hT_g', hT_g'I, h_conj]
  linear_combination ((b : ℂ) * T Complex.I * (1/2 : ℂ)) * hI2

/-! ## Chart-independence of `dbarChart = 0`

If `g` is holomorphic at `z₀` with `g'(z₀) ≠ 0`, then `dbarChart f` at
`g(z₀)` vanishes iff `dbarChart (f ∘ g)` at `z₀` vanishes. This is the
chart-independence statement for the *vanishing* of `∂̄`. -/

/-- **Vanishing of `dbarChart` is chart-invariant** under holomorphic
substitution with nonzero derivative. -/
theorem dbarChart_eq_zero_iff_comp_holomorphicInner {g f : ℂ → ℂ}
    {z₀ g' : ℂ} (hg : HasDerivAt g g' z₀) (hg_ne : g' ≠ 0)
    (hf : DifferentiableAt ℝ f (g z₀)) :
    dbarChart (f ∘ g) z₀ = 0 ↔ dbarChart f (g z₀) = 0 := by
  rw [dbarChart_comp_holomorphicInner hg hf]
  constructor
  · intro h
    have h_conj_ne : (starRingEnd ℂ) g' ≠ 0 := by
      intro hcz
      apply hg_ne
      have hcc : g' = (starRingEnd ℂ) ((starRingEnd ℂ) g') := by
        rw [Complex.conj_conj]
      rw [hcc, hcz, map_zero]
    exact (mul_eq_zero.mp h).resolve_left h_conj_ne
  · intro h
    rw [h, mul_zero]

end JacobianChallenge

end
