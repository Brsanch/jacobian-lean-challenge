/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramWinding
import JacobianChallenge.Analysis.ArctanLinearIntegral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # The parallelogram winding number is `±1`: keystone COMPLETE

**The keystone of `HANDOFF_TLDIVSUM.md`**, in full: for every interior
point `x = a + s·ω₁ + r·ω₂` (`s, r ∈ (0,1)`) of a nondegenerate
parallelogram,

  `∮_{∂Π(a; ω₁, ω₂)} (z − x)⁻¹ dz = ±2πi`,

with the sign that of the lattice orientation `D = ω₁ × ω₂`.

No `Complex.log` branch bookkeeping, no parametric continuity, no
connectivity argument. The proof combines:

* **integrality** (`parallelogram_winding_integrality`): the value is
  `2πi·k`, `k ∈ ℤ`;
* **the angular-velocity computation** (`ArctanLinearIntegral`): the
  imaginary part is a sum of four swept angles whose cross-product
  constants are `rD, (1−s)D, (1−r)D, sD` — all the *same sign* as `D`,
  each of magnitude `< π` (a segment subtends `< π` from an external
  point). Hence `0 < |Im| < 4π`, so `k = ±1`, sign of `D`.

This holds at **every** interior point simultaneously, which is exactly
what the residue side of the forward-Abel contour argument needs.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace JacobianChallenge

namespace ParallelogramWinding

open ArctanLinearIntegral

variable (a ω₁ ω₂ : ℂ)

/-- The orientation cross product `ω₁ × ω₂ = Im(conj ω₁ · ω₂)`. -/
def latticeCross (ω₁ ω₂ : ℂ) : ℝ := ω₁.re * ω₂.im - ω₁.im * ω₂.re

lemma latticeCross_eq_crossIm :
    latticeCross ω₁ ω₂ = crossIm ω₂ ω₁ := by
  rw [latticeCross, crossIm]
  ring

section interior

variable {s r : ℝ}

/-! ## The four cross-product constants at an interior point -/

/-- The interior point. -/
def interiorPt (a ω₁ ω₂ : ℂ) (s r : ℝ) : ℂ := a + s • ω₁ + r • ω₂

lemma cross_side₀ :
    crossIm ω₁ (a - interiorPt a ω₁ ω₂ s r) = r * latticeCross ω₁ ω₂ := by
  rw [crossIm, latticeCross, interiorPt]
  simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

lemma cross_side₁ :
    crossIm ω₂ (a + ω₁ - interiorPt a ω₁ ω₂ s r)
      = (1 - s) * latticeCross ω₁ ω₂ := by
  rw [crossIm, latticeCross, interiorPt]
  simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

lemma cross_side₂ :
    crossIm (-ω₁) (a + ω₁ + ω₂ - interiorPt a ω₁ ω₂ s r)
      = (1 - r) * latticeCross ω₁ ω₂ := by
  rw [crossIm, latticeCross, interiorPt]
  simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im]
  ring

lemma cross_side₃ :
    crossIm (-ω₂) (a + ω₂ - interiorPt a ω₁ ω₂ s r)
      = s * latticeCross ω₁ ω₂ := by
  rw [crossIm, latticeCross, interiorPt]
  simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im]
  ring

/-! ## The sides in `t•α + β` form -/

lemma side₀_sub (t : ℝ) :
    side₀ a ω₁ ω₂ t - interiorPt a ω₁ ω₂ s r
      = t • ω₁ + (a - interiorPt a ω₁ ω₂ s r) := by
  rw [side₀]
  ring

lemma side₁_sub (t : ℝ) :
    side₁ a ω₁ ω₂ t - interiorPt a ω₁ ω₂ s r
      = t • ω₂ + (a + ω₁ - interiorPt a ω₁ ω₂ s r) := by
  rw [side₁]
  ring

lemma side₂_sub (t : ℝ) :
    side₂ a ω₁ ω₂ t - interiorPt a ω₁ ω₂ s r
      = t • (-ω₁) + (a + ω₁ + ω₂ - interiorPt a ω₁ ω₂ s r) := by
  rw [side₂]
  module

lemma side₃_sub (t : ℝ) :
    side₃ a ω₁ ω₂ t - interiorPt a ω₁ ω₂ s r
      = t • (-ω₂) + (a + ω₂ - interiorPt a ω₁ ω₂ s r) := by
  rw [side₃]
  module

end interior

/-! ## Per-side imaginary parts -/

/-- The generic per-side computation: if the side in `t•α + β` form has
nonzero cross constant, the imaginary part of its contour contribution is
the swept-angle integral. -/
lemma im_side_integral (α β x : ℂ) (σ : ℝ → ℂ)
    (hσ : ∀ t : ℝ, σ t - x = t • α + β)
    (hc : crossIm α β ≠ 0) :
    (∫ t in (0 : ℝ)..1, (σ t - x)⁻¹ * α).im
      = ∫ t in (0 : ℝ)..1, crossIm α β / Complex.normSq (t • α + β) := by
  -- The complex integrand in `α / (t•α + β)` form.
  have hfun : (fun t : ℝ => (σ t - x)⁻¹ * α)
      = fun t : ℝ => α / (t • α + β) := by
    funext t
    rw [hσ t, inv_mul_eq_div]
  rw [hfun]
  -- Integrability of the complex integrand.
  have hline : Continuous (fun t : ℝ => t • α + β) := by
    have heq : (fun t : ℝ => t • α + β)
        = fun t : ℝ => (t : ℂ) * α + β := by
      funext t
      rw [Complex.real_smul]
    rw [heq]
    exact (Complex.continuous_ofReal.mul continuous_const).add
      continuous_const
  have hcont : Continuous (fun t : ℝ => α / (t • α + β)) := by
    apply continuous_const.div hline
    intro t
    intro h0
    exact (normSq_line_pos hc t).ne' (by rw [h0]; simp)
  have hii : IntervalIntegrable (fun t : ℝ => α / (t • α + β))
      volume 0 1 := hcont.intervalIntegrable 0 1
  -- Commute `im` with the integral.
  have hcomm := Complex.imCLM.intervalIntegral_comp_comm hii
  have him : (∫ t in (0 : ℝ)..1, α / (t • α + β)).im
      = ∫ t in (0 : ℝ)..1, (α / (t • α + β)).im := by
    calc (∫ t in (0 : ℝ)..1, α / (t • α + β)).im
        = Complex.imCLM (∫ t in (0 : ℝ)..1, α / (t • α + β)) := rfl
      _ = ∫ t in (0 : ℝ)..1, Complex.imCLM (α / (t • α + β)) := by
          rw [hcomm]
      _ = ∫ t in (0 : ℝ)..1, (α / (t • α + β)).im := rfl
  rw [him]
  apply integral_congr
  intro t _
  exact im_div_line hc t

/-! ## The keystone -/

/-- **The parallelogram winding (keystone, complete)**: at every interior
point `x = a + s·ω₁ + r·ω₂`, the boundary integral of `(z − x)⁻¹` is
`±2πi`, with the sign of the orientation `D = ω₁ × ω₂`. -/
theorem boundaryIntegral_inv_sub_interior
    (hD : latticeCross ω₁ ω₂ ≠ 0)
    {s r : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    boundaryIntegral a ω₁ ω₂
        (fun z => (z - interiorPt a ω₁ ω₂ s r)⁻¹)
      = (if 0 < latticeCross ω₁ ω₂ then 1 else -1)
        * (2 * Real.pi * Complex.I) := by
  classical
  set x : ℂ := interiorPt a ω₁ ω₂ s r with hx_def
  set D : ℝ := latticeCross ω₁ ω₂ with hD_def
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨hr0, hr1⟩ := hr
  -- The four cross constants and their nonvanishing.
  have hc₀ : crossIm ω₁ (a - x) = r * D := cross_side₀ a ω₁ ω₂
  have hc₁ : crossIm ω₂ (a + ω₁ - x) = (1 - s) * D := cross_side₁ a ω₁ ω₂
  have hc₂ : crossIm (-ω₁) (a + ω₁ + ω₂ - x) = (1 - r) * D :=
    cross_side₂ a ω₁ ω₂
  have hc₃ : crossIm (-ω₂) (a + ω₂ - x) = s * D := cross_side₃ a ω₁ ω₂
  have hne₀ : crossIm ω₁ (a - x) ≠ 0 := by
    rw [hc₀]; exact mul_ne_zero (ne_of_gt hr0) hD
  have hne₁ : crossIm ω₂ (a + ω₁ - x) ≠ 0 := by
    rw [hc₁]; exact mul_ne_zero (by linarith) hD
  have hne₂ : crossIm (-ω₁) (a + ω₁ + ω₂ - x) ≠ 0 := by
    rw [hc₂]; exact mul_ne_zero (by linarith) hD
  have hne₃ : crossIm (-ω₂) (a + ω₂ - x) ≠ 0 := by
    rw [hc₃]; exact mul_ne_zero (ne_of_gt hs0) hD
  -- The sides avoid `x`.
  have havoid₀ : ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t ≠ x := by
    intro t _ h
    have h2 := normSq_line_pos hne₀ t
    rw [← side₀_sub a ω₁ ω₂ t, h, sub_self] at h2
    simp at h2
  have havoid₁ : ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t ≠ x := by
    intro t _ h
    have h2 := normSq_line_pos hne₁ t
    rw [← side₁_sub a ω₁ ω₂ t, h, sub_self] at h2
    simp at h2
  have havoid₂ : ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t ≠ x := by
    intro t _ h
    have h2 := normSq_line_pos hne₂ t
    rw [← side₂_sub a ω₁ ω₂ t, h, sub_self] at h2
    simp at h2
  have havoid₃ : ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t ≠ x := by
    intro t _ h
    have h2 := normSq_line_pos hne₃ t
    rw [← side₃_sub a ω₁ ω₂ t, h, sub_self] at h2
    simp at h2
  -- Integrality.
  obtain ⟨k, hk⟩ := parallelogram_winding_integrality a ω₁ ω₂ x
    havoid₀ havoid₁ havoid₂ havoid₃
  -- The four swept angles.
  set T₀ : ℝ := ∫ t in (0 : ℝ)..1,
    crossIm ω₁ (a - x) / Complex.normSq (t • ω₁ + (a - x)) with hT₀_def
  set T₁ : ℝ := ∫ t in (0 : ℝ)..1,
    crossIm ω₂ (a + ω₁ - x)
      / Complex.normSq (t • ω₂ + (a + ω₁ - x)) with hT₁_def
  set T₂ : ℝ := ∫ t in (0 : ℝ)..1,
    crossIm (-ω₁) (a + ω₁ + ω₂ - x)
      / Complex.normSq (t • (-ω₁) + (a + ω₁ + ω₂ - x)) with hT₂_def
  set T₃ : ℝ := ∫ t in (0 : ℝ)..1,
    crossIm (-ω₂) (a + ω₂ - x)
      / Complex.normSq (t • (-ω₂) + (a + ω₂ - x)) with hT₃_def
  -- The imaginary part of the boundary integral is the sum of the swept
  -- angles.
  have hIm : (boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹)).im
      = T₀ + T₁ + T₂ + T₃ := by
    rw [boundaryIntegral]
    rw [Complex.add_im, Complex.add_im, Complex.add_im]
    have h0 := im_side_integral ω₁ (a - x) x (side₀ a ω₁ ω₂)
      (side₀_sub a ω₁ ω₂) hne₀
    have h1 := im_side_integral ω₂ (a + ω₁ - x) x (side₁ a ω₁ ω₂)
      (side₁_sub a ω₁ ω₂) hne₁
    have h2 := im_side_integral (-ω₁) (a + ω₁ + ω₂ - x) x (side₂ a ω₁ ω₂)
      (side₂_sub a ω₁ ω₂) hne₂
    have h3 := im_side_integral (-ω₂) (a + ω₂ - x) x (side₃ a ω₁ ω₂)
      (side₃_sub a ω₁ ω₂) hne₃
    beta_reduce
    rw [h0, h1, h2, h3]
  -- The imaginary part of `k·2πi`.
  have hIm2 : (boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹)).im
      = k * (2 * Real.pi) := by
    rw [hk]
    simp [Complex.mul_im]
  -- Case on the sign of `D`.
  rcases lt_or_gt_of_ne hD with hDneg | hDpos
  · -- `D < 0`: all four angles negative, each `> -π`, so `k = -1`.
    have hp₀ : T₀ < 0 := by
      rw [hT₀_def]
      exact integral_crossIm_div_normSq_neg
        (by rw [hc₀]; exact mul_neg_of_pos_of_neg hr0 hDneg)
    have hp₁ : T₁ < 0 := by
      rw [hT₁_def]
      exact integral_crossIm_div_normSq_neg
        (by rw [hc₁]; exact mul_neg_of_pos_of_neg (by linarith) hDneg)
    have hp₂ : T₂ < 0 := by
      rw [hT₂_def]
      exact integral_crossIm_div_normSq_neg
        (by rw [hc₂]; exact mul_neg_of_pos_of_neg (by linarith) hDneg)
    have hp₃ : T₃ < 0 := by
      rw [hT₃_def]
      exact integral_crossIm_div_normSq_neg
        (by rw [hc₃]; exact mul_neg_of_pos_of_neg hs0 hDneg)
    have hb₀ : -Real.pi < T₀ := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₀
      rw [← hT₀_def] at this
      rw [abs_lt] at this
      exact this.1
    have hb₁ : -Real.pi < T₁ := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₁
      rw [← hT₁_def] at this
      rw [abs_lt] at this
      exact this.1
    have hb₂ : -Real.pi < T₂ := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₂
      rw [← hT₂_def] at this
      rw [abs_lt] at this
      exact this.1
    have hb₃ : -Real.pi < T₃ := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₃
      rw [← hT₃_def] at this
      rw [abs_lt] at this
      exact this.1
    -- `-4π < 2πk < 0` forces `k = -1`.
    have hk_eq : k = -1 := by
      have hsum1 : (k : ℝ) * (2 * Real.pi) < 0 := by
        rw [← hIm2, hIm]
        linarith
      have hsum2 : -(4 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by
        rw [← hIm2, hIm]
        linarith
      have hpi := Real.pi_pos
      have hk1 : (k : ℝ) < 0 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      have hk2 : (-2 : ℝ) < (k : ℝ) := by
        by_contra hcon
        push Not at hcon
        nlinarith
      have hkz1 : k < 0 := by exact_mod_cast hk1
      have hkz2 : (-2 : ℤ) < k := by exact_mod_cast hk2
      omega
    rw [hk, hk_eq, if_neg (by linarith : ¬ 0 < D)]
    push_cast
    ring
  · -- `0 < D`: all four angles positive, each `< π`, so `k = 1`.
    have hp₀ : 0 < T₀ := by
      rw [hT₀_def]
      exact integral_crossIm_div_normSq_pos
        (by rw [hc₀]; exact mul_pos hr0 hDpos)
    have hp₁ : 0 < T₁ := by
      rw [hT₁_def]
      exact integral_crossIm_div_normSq_pos
        (by rw [hc₁]; exact mul_pos (by linarith) hDpos)
    have hp₂ : 0 < T₂ := by
      rw [hT₂_def]
      exact integral_crossIm_div_normSq_pos
        (by rw [hc₂]; exact mul_pos (by linarith) hDpos)
    have hp₃ : 0 < T₃ := by
      rw [hT₃_def]
      exact integral_crossIm_div_normSq_pos
        (by rw [hc₃]; exact mul_pos hs0 hDpos)
    have hb₀ : T₀ < Real.pi := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₀
      rw [← hT₀_def] at this
      rw [abs_lt] at this
      exact this.2
    have hb₁ : T₁ < Real.pi := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₁
      rw [← hT₁_def] at this
      rw [abs_lt] at this
      exact this.2
    have hb₂ : T₂ < Real.pi := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₂
      rw [← hT₂_def] at this
      rw [abs_lt] at this
      exact this.2
    have hb₃ : T₃ < Real.pi := by
      have := abs_integral_crossIm_div_normSq_lt_pi hne₃
      rw [← hT₃_def] at this
      rw [abs_lt] at this
      exact this.2
    -- `0 < 2πk < 4π` forces `k = 1`.
    have hk_eq : k = 1 := by
      have hsum1 : 0 < (k : ℝ) * (2 * Real.pi) := by
        rw [← hIm2, hIm]
        linarith
      have hsum2 : (k : ℝ) * (2 * Real.pi) < 4 * Real.pi := by
        rw [← hIm2, hIm]
        linarith
      have hpi := Real.pi_pos
      have hk1 : (0 : ℝ) < (k : ℝ) := by
        by_contra hcon
        push Not at hcon
        nlinarith
      have hk2 : (k : ℝ) < 2 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      have hkz1 : (0 : ℤ) < k := by exact_mod_cast hk1
      have hkz2 : k < 2 := by exact_mod_cast hk2
      omega
    rw [hk, hk_eq]
    rw [if_pos hDpos]
    push_cast
    ring

end ParallelogramWinding

end JacobianChallenge

end
