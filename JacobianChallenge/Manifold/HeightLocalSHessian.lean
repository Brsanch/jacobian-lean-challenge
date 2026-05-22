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

/-! # The Hessian of `heightLocalℂ_S` at `w = 0` (classical-5)

Parallel to classical-4 (chartN-side `heightLocalℂ` Hessian) but for the
chartS-side `heightLocalℂ_S w = ‖w‖² / (1 + ‖w‖²)` at the critical point
`w = 0` (which lifts to `∞ : RiemannSphere`).

At `w = 0`, the second derivative of `heightLocalℂ_S` is the
*positive*-definite bilinear form `+2 · innerSL ℝ` on `ℂ ≅ ℝ²`. Hence
`heightLocalℂ_S` is Morse at `0` (local **min** with non-degenerate
Hessian).

Approach (parallel to classical-4 with signs flipped):

* `fderiv ℝ heightLocalℂ_S z = ((1+‖z‖²)²)⁻¹ • (2 • innerSL ℝ z)` —
  obtained via the chain rule on `(fun y => 1 - y⁻¹) ∘ (1 + ‖·‖²)`,
  using the pointwise identity `‖w‖²/(1+‖w‖²) = 1 - (1+‖w‖²)⁻¹`.
* At `z = 0` the outer scalar `c'(0) = 1` (vs `c(0) = -1` for `heightLocalℂ`),
  so the second derivative at 0 picks up `+2 • innerSL ℝ` (vs `-2 • innerSL ℝ`).
* Non-degeneracy: pick w = 1 (gets `Re v = 0`), w = I (gets `Im v = 0`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace RiemannSphere

/-- **Step 1: Global formula for `fderiv ℝ heightLocalℂ_S z`.** Chain
rule on `(fun y => 1 - y⁻¹) ∘ (1 + ‖·‖²)`. -/
lemma fderiv_heightLocalℂ_S (z : ℂ) :
    fderiv ℝ heightLocalℂ_S z =
      (((1 + ‖z‖^2)^2)⁻¹) • ((2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ)) := by
  have h_pos : (0 : ℝ) < 1 + ‖z‖^2 := by positivity
  have h_ne : (1 + ‖z‖^2 : ℝ) ≠ 0 := h_pos.ne'
  have h_denom : HasFDerivAt (fun w : ℂ => 1 + ‖w‖^2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1
  have h_inv : HasDerivAt (fun y : ℝ => y⁻¹)
      (-((1 + ‖z‖^2)^2)⁻¹) (1 + ‖z‖^2) := hasDerivAt_inv h_ne
  -- (fun y => 1 - y⁻¹) has derivative -(-((·)²)⁻¹) = ((·)²)⁻¹.
  have h_outer : HasDerivAt (fun y : ℝ => 1 - y⁻¹)
      (((1 + ‖z‖^2)^2)⁻¹) (1 + ‖z‖^2) := by
    have h := h_inv.const_sub (1 : ℝ)
    -- h : HasDerivAt (fun y => 1 - y⁻¹) (-(-((1+‖z‖²)²)⁻¹)) (1+‖z‖²)
    convert h using 1
    ring
  have h_comp_raw := h_outer.comp_hasFDerivAt z h_denom
  have h_comp : HasFDerivAt heightLocalℂ_S
      (((1 + ‖z‖^2)^2)⁻¹ • (2 • innerSL ℝ z)) z := by
    apply h_comp_raw.congr_of_eventuallyEq
    filter_upwards [Filter.univ_mem] with w _
    show heightLocalℂ_S w = ((fun y : ℝ => 1 - y⁻¹) ∘ fun w : ℂ => 1 + ‖w‖^2) w
    show heightLocalℂ_S w = 1 - (1 + ‖w‖^2)⁻¹
    unfold heightLocalℂ_S
    have h_pos' : (0 : ℝ) < 1 + ‖w‖^2 := by positivity
    have h_ne' : (1 + ‖w‖^2 : ℝ) ≠ 0 := h_pos'.ne'
    field_simp
    ring
  exact h_comp.fderiv

/-- **Step 2: `fderiv ℝ (fderiv ℝ heightLocalℂ_S) 0 v = 2 • innerSL ℝ v`**
as a continuous linear map `ℂ →L[ℝ] ℝ`. -/
lemma fderiv_fderiv_heightLocalℂ_S_zero (v : ℂ) :
    fderiv ℝ (fderiv ℝ heightLocalℂ_S) 0 v
      = (2 : ℝ) • (innerSL ℝ v : ℂ →L[ℝ] ℝ) := by
  -- By Step 1, fderiv ℝ heightLocalℂ_S = (z ↦ c'(z) • g(z)) where
  -- c'(z) = ((1+‖z‖²)²)⁻¹ : ℂ → ℝ, c'(0) = 1
  -- g(z)  = 2 • innerSL ℝ z : ℂ → (ℂ →L[ℝ] ℝ), g(0) = 0
  have h_funext : fderiv ℝ heightLocalℂ_S =
      (fun z : ℂ => (((1 + ‖z‖^2)^2)⁻¹) •
        ((2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ))) := by
    funext z
    exact fderiv_heightLocalℂ_S z
  rw [h_funext]
  -- p(z) := 1 + ‖z‖² : HasFDerivAt p 0 0 (since norm_sq has zero deriv at 0).
  have h_p_at_zero : HasFDerivAt (fun z : ℂ => 1 + ‖z‖^2) (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h_raw := (hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt.const_add 1
    have h_zero : (2 : ℕ) • (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
      have : (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
        ext w
        simp [innerSL_apply_apply]
      rw [this]
      simp
    rw [h_zero] at h_raw
    exact h_raw
  -- Outer: (fun t : ℝ => (t^2)⁻¹). Derivative at 1: -(2)/(1^2)^2 = -2.
  have h_outer : HasDerivAt (fun t : ℝ => (t^2)⁻¹) (-2 : ℝ) 1 := by
    have h_sq : HasDerivAt (fun t : ℝ => t^2) (2 : ℝ) 1 := by
      simpa using (hasDerivAt_pow 2 (1 : ℝ))
    have h_ne : ((1 : ℝ))^2 ≠ 0 := by norm_num
    have h_inv : HasDerivAt (fun t : ℝ => (t^2)⁻¹) (-(2 : ℝ) / ((1^2)^2)) (1 : ℝ) :=
      h_sq.inv h_ne
    have h_eq : -(2 : ℝ) / ((1^2)^2) = -2 := by norm_num
    rw [h_eq] at h_inv
    exact h_inv
  have h_c_at_zero : HasFDerivAt (fun z : ℂ => ((1 + ‖z‖^2)^2)⁻¹)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h_one_eq : (1 + ‖(0 : ℂ)‖^2 : ℝ) = 1 := by simp
    have h_outer' : HasDerivAt (fun t : ℝ => (t^2)⁻¹) (-2) (1 + ‖(0 : ℂ)‖^2) := by
      rw [h_one_eq]; exact h_outer
    have h_comp := h_outer'.comp_hasFDerivAt (0 : ℂ) h_p_at_zero
    have h_smul_zero : ((-2 : ℝ) • (0 : ℂ →L[ℝ] ℝ)) = 0 := by simp
    rw [h_smul_zero] at h_comp
    apply h_comp.congr_of_eventuallyEq
    filter_upwards [Filter.univ_mem] with z _
    show ((1 + ‖z‖^2)^2)⁻¹ =
      ((fun t : ℝ => (t^2)⁻¹) ∘ (fun z : ℂ => 1 + ‖z‖^2)) z
    rfl
  -- g(z) := (2 : ℕ) • innerSL ℝ z. As CLM-valued: HasFDerivAt g (2 • innerSL ℝ) at 0.
  have h_innerSL : HasFDerivAt (fun z : ℂ => (innerSL ℝ z : ℂ →L[ℝ] ℝ))
      (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) 0 :=
    (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).hasFDerivAt
  have h_g_at_zero : HasFDerivAt
      (fun z : ℂ => (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ))
      ((2 : ℕ) • (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)) 0 :=
    h_innerSL.const_smul (2 : ℕ)
  -- Combine via HasFDerivAt.smul (c'(z) scalar-valued, g(z) CLM-valued).
  have h_combined := h_c_at_zero.smul h_g_at_zero
  have h_fn_eq :
      ((fun z : ℂ => ((1 + ‖z‖^2)^2)⁻¹) • fun z : ℂ => (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ))
      = (fun z : ℂ => ((1 + ‖z‖^2)^2)⁻¹ • (2 : ℕ) • (innerSL ℝ z : ℂ →L[ℝ] ℝ)) := by
    funext z; rfl
  rw [h_fn_eq] at h_combined
  rw [h_combined.fderiv]
  -- After .fderiv, lambdas beta-reduced. Goal:
  -- (((1 + ‖0‖²)²)⁻¹ • 2 • innerSL ℝ + smulRight 0 (2 • innerSL ℝ 0)) v = (2 : ℝ) • innerSL ℝ v
  -- Substitute the scalar c'(0) = 1 and inner CLM `innerSL ℝ 0 = 0` (which kills smulRight).
  have hc0' : ((1 + ‖(0 : ℂ)‖^2)^2)⁻¹ = (1 : ℝ) := by simp
  have h_inner_zero : (innerSL ℝ (0 : ℂ) : ℂ →L[ℝ] ℝ) = 0 := by
    ext z; simp
  rw [hc0', h_inner_zero]
  -- Goal: ((1 : ℝ) • 2 • innerSL ℝ + smulRight 0 (2 • 0)) v = (2 : ℝ) • innerSL ℝ v
  rw [smul_zero, one_smul]
  -- Goal: (2 • innerSL ℝ + smulRight 0 0) v = (2 : ℝ) • innerSL ℝ v
  have hsr : ContinuousLinearMap.smulRight (0 : ℂ →L[ℝ] ℝ) (0 : ℂ →L[ℝ] ℝ) = 0 := by
    ext z; simp
  rw [hsr, add_zero]
  -- Goal: ((2 : ℕ) • innerSL ℝ) v = (2 : ℝ) • innerSL ℝ v
  ext w
  -- LHS: ((2 : ℕ) • F) v w = ((F + F) v) w = F v w + F v w  via two_nsmul + defeq + add_apply.
  -- RHS: ((2 : ℝ) • G) w = 2 * G w  via smul_apply + smul_eq_mul.
  rw [two_nsmul]
  -- Goal: ((innerSL ℝ + innerSL ℝ) v) w = ((2 : ℝ) • innerSL ℝ v) w
  -- (F + G) v reduces by defeq to F v + G v on CLMs.
  change ((innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) v + (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) v) w
       = ((2 : ℝ) • (innerSL ℝ v : ℂ →L[ℝ] ℝ)) w
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The Hessian formula at w = 0** in `iteratedFDeriv ℝ 2` form. -/
theorem heightLocalℂ_S_iteratedFDeriv_two_apply (v w : ℂ) :
    iteratedFDeriv ℝ 2 heightLocalℂ_S 0 ![v, w]
      = 2 * (v.re * w.re + v.im * w.im) := by
  rw [iteratedFDeriv_two_apply]
  show fderiv ℝ (fderiv ℝ heightLocalℂ_S) 0 v w = 2 * (v.re * w.re + v.im * w.im)
  rw [fderiv_fderiv_heightLocalℂ_S_zero v]
  rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  show (2 : ℝ) * @inner ℝ ℂ _ v w = 2 * (v.re * w.re + v.im * w.im)
  congr 1
  show @inner ℝ ℂ _ v w = v.re * w.re + v.im * w.im
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Non-degeneracy of `heightLocalℂ_S`'s Hessian at w = 0.** If
`∀ w, iteratedFDeriv ℝ 2 heightLocalℂ_S 0 ![v, w] = 0`, then `v = 0`. -/
theorem heightLocalℂ_S_hessian_nondeg_at_zero (v : ℂ)
    (h : ∀ w : ℂ, iteratedFDeriv ℝ 2 heightLocalℂ_S 0 ![v, w] = 0) :
    v = 0 := by
  -- Pick w = 1: gives 2 · v.re = 0, so v.re = 0.
  have h1 := h 1
  rw [heightLocalℂ_S_iteratedFDeriv_two_apply v 1] at h1
  simp [Complex.one_re, Complex.one_im] at h1
  -- Pick w = I: gives 2 · v.im = 0, so v.im = 0.
  have hi := h Complex.I
  rw [heightLocalℂ_S_iteratedFDeriv_two_apply v Complex.I] at hi
  simp [Complex.I_re, Complex.I_im] at hi
  exact Complex.ext h1 hi

end RiemannSphere

end JacobianChallenge

end
