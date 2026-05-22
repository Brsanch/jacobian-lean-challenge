/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import JacobianChallenge.Manifold.MorseFunctionRiemannSphere

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # The Hessian of `heightLocalℂ` at `z = 0` (classical-4)

The Hessian computation: at `z = 0`, the second derivative of
`heightLocalℂ z = 1/(1 + ‖z‖²)` is the negative-definite bilinear
form `-2 · innerSL ℝ` on `ℂ ≅ ℝ²`. Hence `heightLocalℂ` is Morse at
`0` (local max with non-degenerate Hessian).

Approach:

* `fderiv ℝ heightLocalℂ z = (-((1+‖z‖²)²)⁻¹) • (2 • innerSL ℝ z)` —
  the chain-rule fact in tree (chip 47).
* Differentiate this at `z = 0` using product rule. At z=0:
  - `c(0) = -1`, `fderiv c 0 = 0` (since `(1+‖·‖²)` has zero deriv at 0).
  - `innerSL ℝ 0 = 0`, `fderiv (z ↦ 2 • innerSL ℝ z) 0 = 2 • innerSL ℝ`
    (linear map).
* Therefore `fderiv ℝ (fderiv ℝ heightLocalℂ) 0 v = -2 • innerSL ℝ v`.
* Hence `iteratedFDeriv ℝ 2 heightLocalℂ 0 ![v, w] = -2 · inner v w`.
* Non-degenerate: pick w = 1 (gets Re v = 0), w = I (gets Im v = 0).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace RiemannSphere

/-- **Step 1: Global formula for `fderiv ℝ heightLocalℂ z`.** Just
extracts the chain-rule fact from chip 47 globally. -/
lemma fderiv_heightLocalℂ (z : ℂ) :
    fderiv ℝ heightLocalℂ z =
      (-((1 + ‖z‖^2)^2)⁻¹) • ((2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ)) := by
  have h_pos : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
  have h_ne : (1 + ‖z‖^2 : ℝ) ≠ 0 := h_pos.ne'
  have h_denom : HasFDerivAt (fun w : ℂ => 1 + ‖w‖^2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1
  have h_inv : HasDerivAt (fun y : ℝ => y⁻¹)
      (-((1 + ‖z‖^2)^2)⁻¹) (1 + ‖z‖^2) := hasDerivAt_inv h_ne
  have h_comp_raw := h_inv.comp_hasFDerivAt z h_denom
  have h_comp : HasFDerivAt heightLocalℂ
      ((-((1 + ‖z‖^2)^2)⁻¹) • (2 • innerSL ℝ z)) z := by
    apply h_comp_raw.congr_of_eventuallyEq
    filter_upwards [Filter.univ_mem] with w _
    show heightLocalℂ w = ((fun y : ℝ => y⁻¹) ∘ fun w : ℂ => 1 + ‖w‖^2) w
    show heightLocalℂ w = (1 + ‖w‖^2)⁻¹
    unfold heightLocalℂ
    rw [one_div]
  exact h_comp.fderiv

/-- **Step 2: `fderiv ℝ (fderiv ℝ heightLocalℂ) 0 v = -2 • innerSL ℝ v`**
as a continuous linear map `ℂ →L[ℝ] ℝ`. -/
lemma fderiv_fderiv_heightLocalℂ_zero (v : ℂ) :
    fderiv ℝ (fderiv ℝ heightLocalℂ) 0 v
      = (-2 : ℝ) • (innerSL ℝ v : ℂ →L[ℝ] ℝ) := by
  -- The function `z ↦ fderiv ℝ heightLocalℂ z` equals
  -- `z ↦ (-((1+‖z‖²)²)⁻¹) • (2 • innerSL ℝ z)` globally (by Step 1).
  -- So fderiv at 0 equals fderiv of that at 0.
  have h_funext : fderiv ℝ heightLocalℂ =
      (fun z : ℂ => (-((1 + ‖z‖^2)^2)⁻¹) •
        ((2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ))) := by
    funext z
    exact fderiv_heightLocalℂ z
  rw [h_funext]
  -- Now goal: fderiv ℝ (fun z => c(z) • g(z)) 0 v = -2 • innerSL ℝ v
  -- where c(z) := -((1+‖z‖²)²)⁻¹ : ℂ → ℝ and g(z) := 2 • innerSL ℝ z.
  -- Use HasFDerivAt.smul with product rule.
  -- At z=0: c(0) = -1, fderiv c 0 = 0, g(0) = 0, fderiv g 0 = 2 • innerSL ℝ.
  -- Result: (c(0) • fderiv g 0 + fderiv c 0 • g(0)) v
  --       = (-1 • (2 • innerSL ℝ) + 0 • 0) v = -2 • innerSL ℝ v.
  --
  -- Build HasFDerivAt for c and g separately, then combine.
  -- c(z) = -((1+‖z‖²)²)⁻¹ : factor as composition.
  -- p(z) := 1 + ‖z‖² : ℂ → ℝ. HasFDerivAt p 0 0 (since norm_sq has zero
  -- derivative at 0).
  have h_p_at_zero : HasFDerivAt (fun z : ℂ => 1 + ‖z‖^2) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h_raw := (hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt.const_add 1
    -- h_raw : HasFDerivAt _ (2 • innerSL ℝ (0:ℂ)) 0
    -- And innerSL ℝ (0 : ℂ) = 0 as a CLM.
    have h_zero : (2 : ℕ) • (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
      have : (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
        ext w
        simp [innerSL_apply_apply]
      rw [this]
      simp
    rw [h_zero] at h_raw
    exact h_raw
  -- Now c(z) = (fun t : ℝ => -(t^2)⁻¹) ∘ p. HasDerivAt of the outer at p(0) = 1.
  have h_outer : HasDerivAt (fun t : ℝ => -(t^2)⁻¹) (2 : ℝ) 1 := by
    have h_sq : HasDerivAt (fun t : ℝ => t^2) (2 : ℝ) 1 := by
      simpa using (hasDerivAt_pow 2 (1 : ℝ))
    have h_ne : ((1 : ℝ))^2 ≠ 0 := by norm_num
    -- HasDerivAt.inv: f has derivative f' at x, f x ≠ 0 ⇒ 1/f has deriv -f'/(f x)².
    have h_inv : HasDerivAt (fun t : ℝ => (t^2)⁻¹) (-(2 : ℝ) / ((1^2)^2)) (1 : ℝ) :=
      h_sq.inv h_ne
    have h_neg : HasDerivAt (fun t : ℝ => -((t^2)⁻¹))
        (-(-(2 : ℝ) / ((1^2)^2))) (1 : ℝ) := h_inv.neg
    have h_eq : -(-(2 : ℝ) / ((1^2)^2)) = 2 := by norm_num
    rw [h_eq] at h_neg
    exact h_neg
  have h_c_at_zero : HasFDerivAt (fun z : ℂ => -((1 + ‖z‖^2)^2)⁻¹)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h_one_eq : (1 + ‖(0 : ℂ)‖^2 : ℝ) = 1 := by simp
    have h_outer' : HasDerivAt (fun t : ℝ => -(t^2)⁻¹) 2 (1 + ‖(0 : ℂ)‖^2) := by
      rw [h_one_eq]; exact h_outer
    have h_comp := h_outer'.comp_hasFDerivAt (0 : ℂ) h_p_at_zero
    -- h_comp : HasFDerivAt ((fun t => -(t^2)⁻¹) ∘ p) ((2 : ℝ) • (0 : ℂ →L[ℝ] ℝ)) 0
    have h_smul_zero : ((2 : ℝ) • (0 : ℂ →L[ℝ] ℝ)) = 0 := by simp
    rw [h_smul_zero] at h_comp
    -- Now congr to match the actual function.
    apply h_comp.congr_of_eventuallyEq
    filter_upwards [Filter.univ_mem] with z _
    show -((1 + ‖z‖^2)^2)⁻¹ =
      ((fun t : ℝ => -(t^2)⁻¹) ∘ (fun z : ℂ => 1 + ‖z‖^2)) z
    rfl
  -- g(z) := (2 : ℕ) • innerSL ℝ z. As a function ℂ → ℂ →L[ℝ] ℝ, this is
  -- (2 : ℕ) • innerSL ℝ (the bilinear-as-linear-in-first-arg evaluated at z).
  -- It's a continuous linear map ℂ → (ℂ →L[ℝ] ℝ) — its fderiv at 0 equals
  -- the CLM itself.
  -- innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) is a CLM (linear in first arg).
  -- fderiv at any point = innerSL ℝ.
  have h_innerSL : HasFDerivAt (fun z : ℂ => (innerSL ℝ z : ℂ →L[ℝ] ℝ))
      (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) 0 :=
    (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).hasFDerivAt
  -- Multiplied by (2 : ℕ) (i.e., 2-times).
  have h_g_at_zero : HasFDerivAt
      (fun z : ℂ => (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ))
      ((2 : ℕ) • (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) 0 := by
    -- HasFDerivAt.const_smul with (2 : ℕ).
    exact h_innerSL.const_smul (2 : ℕ)
  -- Combine via HasFDerivAt.smul (c is the scalar-valued, g is the
  -- vector-valued).
  have h_combined := h_c_at_zero.smul h_g_at_zero
  -- h_combined : HasFDerivAt (fun z => c(z) • g(z)) D 0 where
  -- D = c(0) • fderiv g 0 + ContinuousLinearMap.smulRight (fderiv c 0) (g 0).
  -- Compute D applied to v:
  -- D v = c(0) • (fderiv g 0) v + ((fderiv c 0) v) • g(0)
  --     = (-1) • (2 • innerSL ℝ v) + (0 v) • g(0)
  --     = -2 • innerSL ℝ v + 0
  --     = -2 • innerSL ℝ v.
  -- Apply .fderiv and evaluate. The combined function uses `Pi.smul`
  -- (two-function smul) but our target uses `fun z => c(z) • g(z)`
  -- (single-function with inner smul). They're equal as functions.
  have h_fn_eq :
      ((fun z : ℂ => -((1 + ‖z‖^2)^2)⁻¹) • fun z : ℂ => (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ))
      = (fun z : ℂ => -((1 + ‖z‖^2)^2)⁻¹ • (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ)) := by
    funext z; rfl
  rw [h_fn_eq] at h_combined
  rw [h_combined.fderiv]
  -- Goal: (c(0) • (2 • innerSL ℝ) + smulRight 0 (g 0)) v = -2 • innerSL ℝ v
  -- Simplify c(0) and the smulRight-with-zero.
  have hc0 : (fun z : ℂ => -((1 + ‖z‖^2)^2)⁻¹) 0 = -1 := by
    simp
  have hg0 : (fun z : ℂ => (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ)) 0 = 0 := by
    show (2 : ℕ) • (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0
    have : (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
      ext w; simp [innerSL_apply_apply]
    rw [this]; simp
  -- After unfolding, apply at v.
  ext w
  -- Goal: ((c 0) • (fderiv g 0) + smulRight (fderiv c 0) (g 0)) v w
  --     = ((-2 : ℝ) • innerSL ℝ v) w
  -- The LHS is a CLM applied to w; the inner CLM is `fderiv ...` applied to v.
  -- Direct simplification: ‖0‖² = 0, so the c(0) factor becomes -1;
  -- innerSL ℝ 0 = 0 zero CLM, so the smulRight 0 (g 0) term has the
  -- inner CLM zero (zero applied to v = 0).
  have h_inner_zero : (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
    ext z; simp [innerSL_apply_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.zero_apply,
    h_inner_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, inv_one, neg_neg, one_smul, mul_zero, smul_zero,
    Nat.cast_ofNat, smul_eq_mul, one_pow]
  -- Convert to multiplication form via show/rfl unfolding of nested smul.
  show (-1 : ℝ) * ((2 : ℕ) • (((innerSL ℝ) v) w : ℝ))
       = -2 * ((innerSL ℝ) v) w
  rw [nsmul_eq_mul]
  push_cast
  ring

/-- **The Hessian formula at z = 0** in `iteratedFDeriv ℝ 2` form. -/
theorem heightLocalℂ_iteratedFDeriv_two_apply (v w : ℂ) :
    iteratedFDeriv ℝ 2 heightLocalℂ 0 ![v, w]
      = -2 * (v.re * w.re + v.im * w.im) := by
  rw [iteratedFDeriv_two_apply]
  -- Goal: fderiv ℝ (fderiv ℝ heightLocalℂ) 0 (![v, w] 0) (![v, w] 1) = ...
  show fderiv ℝ (fderiv ℝ heightLocalℂ) 0 v w = -2 * (v.re * w.re + v.im * w.im)
  rw [fderiv_fderiv_heightLocalℂ_zero v]
  -- Goal: ((-2 : ℝ) • innerSL ℝ v) w = -2 * (v.re * w.re + v.im * w.im)
  rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  show (-2 : ℝ) * @inner ℝ ℂ _ v w = -2 * (v.re * w.re + v.im * w.im)
  congr 1
  -- inner ℝ on ℂ: ⟨v, w⟩_ℝ = (w * conj v).re = v.re*w.re + v.im*w.im.
  show @inner ℝ ℂ _ v w = v.re * w.re + v.im * w.im
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Non-degeneracy of `heightLocalℂ`'s Hessian at z = 0.** If
`∀ w, iteratedFDeriv ℝ 2 heightLocalℂ 0 ![v, w] = 0`, then `v = 0`. -/
theorem heightLocalℂ_hessian_nondeg_at_zero (v : ℂ)
    (h : ∀ w : ℂ, iteratedFDeriv ℝ 2 heightLocalℂ 0 ![v, w] = 0) :
    v = 0 := by
  -- Pick w = 1: gives -2 · v.re = 0, so v.re = 0.
  have h1 := h 1
  rw [heightLocalℂ_iteratedFDeriv_two_apply v 1] at h1
  -- h1 : -2 * (v.re * 1.re + v.im * 1.im) = 0
  -- Simplify: -2 * (v.re * 1 + v.im * 0) = 0 ⇒ v.re = 0.
  simp [Complex.one_re, Complex.one_im] at h1
  -- Pick w = I: gives -2 · v.im = 0, so v.im = 0.
  have hi := h Complex.I
  rw [heightLocalℂ_iteratedFDeriv_two_apply v Complex.I] at hi
  simp [Complex.I_re, Complex.I_im] at hi
  exact Complex.ext h1 hi

end RiemannSphere

end JacobianChallenge

end
