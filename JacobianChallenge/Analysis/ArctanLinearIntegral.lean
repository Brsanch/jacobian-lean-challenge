/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.Basic

set_option linter.unusedSectionVars false

/-! # The angular-velocity integral along a complex segment

For `α β : ℂ` with nonzero cross product `c := α.im·β.re − α.re·β.im`
(equivalently `(α·conj β).im ≠ 0`, i.e. the line `t ↦ t·α + β` misses the
origin), the imaginary part of `α / (t·α + β)` is the **angular
velocity** `c / |tα + β|²` of the segment as seen from `0`, and its
integral over `[0,1]` is an arctan difference:

* `integral_crossIm_div_normSq` — the exact arctan evaluation (no branch
  cuts: everything is real);
* `abs_integral_crossIm_div_normSq_lt_pi` — the swept angle of a segment
  seen from an external point is **strictly less than `π`**;
* `integral_crossIm_div_normSq_pos/neg` — its sign is the sign of `c`.

These three facts are the per-side input of the parallelogram winding
evaluation (`HANDOFF_TLDIVSUM.md`, keystone): combined with the already
proven `2πi·ℤ` membership they pin the winding to `±2πi` at every
interior point, with no `Complex.log` branch bookkeeping and no
parametric-continuity argument.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace JacobianChallenge

namespace ArctanLinearIntegral

/-- The cross product `α × β` of two complex numbers viewed as plane
vectors; equals `(α * conj β).im` up to sign convention: this is
`α.im * β.re - α.re * β.im = -(α * conj β).im`... we fix the convention
`crossIm α β = α.im * β.re - α.re * β.im`. -/
def crossIm (α β : ℂ) : ℝ := α.im * β.re - α.re * β.im

/-- The dot product `⟨α, β⟩` of two complex numbers as plane vectors. -/
def dotRe (α β : ℂ) : ℝ := α.re * β.re + α.im * β.im

variable {α β : ℂ}

/-- Nonzero cross product forces `α ≠ 0`. -/
lemma alpha_ne_zero (hc : crossIm α β ≠ 0) : α ≠ 0 := by
  intro h
  apply hc
  rw [crossIm, h]
  simp

/-- Nonzero cross product forces `normSq α > 0`. -/
lemma normSq_alpha_pos (hc : crossIm α β ≠ 0) : 0 < Complex.normSq α :=
  Complex.normSq_pos.mpr (alpha_ne_zero hc)

/-- The segment `t ↦ t•α + β` misses the origin when the cross product is
nonzero. -/
lemma normSq_line_pos (hc : crossIm α β ≠ 0) (t : ℝ) :
    0 < Complex.normSq (t • α + β) := by
  rw [Complex.normSq_pos]
  intro h0
  apply hc
  have hre : t * α.re + β.re = 0 := by
    have := congrArg Complex.re h0
    simpa [Complex.add_re] using this
  have him : t * α.im + β.im = 0 := by
    have := congrArg Complex.im h0
    simpa [Complex.add_im] using this
  have hbre : β.re = -(t * α.re) := by linarith
  have hbim : β.im = -(t * α.im) := by linarith
  rw [crossIm, hbre, hbim]
  ring

/-- **Pointwise angular velocity**: the imaginary part of `α / (t•α + β)`
is `crossIm α β / |t•α + β|²`. -/
lemma im_div_line (hc : crossIm α β ≠ 0) (t : ℝ) :
    (α / (t • α + β)).im
      = crossIm α β / Complex.normSq (t • α + β) := by
  have hQ := (normSq_line_pos hc t).ne'
  rw [Complex.div_im]
  rw [div_sub_div_same]
  congr 1
  have hre : (t • α + β).re = t * α.re + β.re := by
    simp [Complex.add_re]
  have him : (t • α + β).im = t * α.im + β.im := by
    simp [Complex.add_im]
  rw [hre, him, crossIm]
  ring

/-- **The Lagrange completion**: `|t•α + β|² · |α|² = (|α|²t + ⟨α,β⟩)² +
(α × β)²`. -/
lemma normSq_line_mul (t : ℝ) :
    Complex.normSq (t • α + β) * Complex.normSq α
      = (Complex.normSq α * t + dotRe α β) ^ 2 + crossIm α β ^ 2 := by
  have hre : (t • α + β).re = t * α.re + β.re := by
    simp [Complex.add_re]
  have him : (t • α + β).im = t * α.im + β.im := by
    simp [Complex.add_im]
  rw [Complex.normSq_apply, Complex.normSq_apply, hre, him, dotRe, crossIm]
  ring

/-- **The arctan primitive**: `u ↦ arctan ((|α|²u + ⟨α,β⟩)/(α×β))`
differentiates to the angular velocity. -/
lemma hasDerivAt_arctan_primitive (hc : crossIm α β ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => Real.arctan
        ((Complex.normSq α * u + dotRe α β) / crossIm α β))
      (crossIm α β / Complex.normSq (t • α + β)) t := by
  set P : ℝ := Complex.normSq α with hP_def
  set q : ℝ := dotRe α β with hq_def
  set c : ℝ := crossIm α β with hc_def
  have hP : 0 < P := normSq_alpha_pos hc
  have hQ : 0 < Complex.normSq (t • α + β) := normSq_line_pos hc t
  -- The inner linear map.
  have hinner : HasDerivAt (fun u : ℝ => (P * u + q) / c) (P / c) t := by
    have h1 : HasDerivAt (fun u : ℝ => P * u + q) P t := by
      have h2 := ((hasDerivAt_id t).const_mul P).add_const q
      simpa using h2
    exact h1.div_const c
  -- Compose with arctan.
  have harctan := (Real.hasDerivAt_arctan ((P * t + q) / c)).comp t hinner
  -- Identify the derivative value.
  have hkey : Complex.normSq (t • α + β) * P = (P * t + q) ^ 2 + c ^ 2 :=
    normSq_line_mul t
  have hval : 1 / (1 + ((P * t + q) / c) ^ 2) * (P / c)
      = c / Complex.normSq (t • α + β) := by
    have hQP : Complex.normSq (t • α + β) = ((P * t + q) ^ 2 + c ^ 2) / P := by
      field_simp
      linarith [hkey]
    rw [hQP]
    field_simp
    ring
  rw [hval] at harctan
  exact harctan

/-- **The swept-angle integral**: exact arctan evaluation. -/
theorem integral_crossIm_div_normSq (hc : crossIm α β ≠ 0) :
    (∫ t in (0 : ℝ)..1, crossIm α β / Complex.normSq (t • α + β))
      = Real.arctan
          ((Complex.normSq α * 1 + dotRe α β) / crossIm α β)
        - Real.arctan
          ((Complex.normSq α * 0 + dotRe α β) / crossIm α β) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- Continuity of the integrand.
  have hcont : Continuous
      (fun t : ℝ => crossIm α β / Complex.normSq (t • α + β)) := by
    have hline : Continuous (fun t : ℝ => t • α + β) := by
      have heq : (fun t : ℝ => t • α + β)
          = fun t : ℝ => (t : ℂ) * α + β := by
        funext t
        rw [Complex.real_smul]
      rw [heq]
      exact (Complex.continuous_ofReal.mul continuous_const).add
        continuous_const
    apply continuous_const.div
    · exact Complex.continuous_normSq.comp hline
    · exact fun t => (normSq_line_pos hc t).ne'
  exact integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_arctan_primitive hc t)
    (hcont.intervalIntegrable 0 1)

/-- **Strict π bound on the swept angle.** -/
theorem abs_integral_crossIm_div_normSq_lt_pi (hc : crossIm α β ≠ 0) :
    |∫ t in (0 : ℝ)..1, crossIm α β / Complex.normSq (t • α + β)|
      < Real.pi := by
  rw [integral_crossIm_div_normSq hc]
  set u : ℝ := (Complex.normSq α * 1 + dotRe α β) / crossIm α β
  set v : ℝ := (Complex.normSq α * 0 + dotRe α β) / crossIm α β
  have hu₁ : Real.arctan u < Real.pi / 2 := Real.arctan_lt_pi_div_two u
  have hu₂ : -(Real.pi / 2) < Real.arctan u := Real.neg_pi_div_two_lt_arctan u
  have hv₁ : Real.arctan v < Real.pi / 2 := Real.arctan_lt_pi_div_two v
  have hv₂ : -(Real.pi / 2) < Real.arctan v := Real.neg_pi_div_two_lt_arctan v
  rw [abs_lt]
  constructor <;> linarith

/-- **Positive sign**: positive cross product gives a positive swept
angle. -/
theorem integral_crossIm_div_normSq_pos (hcpos : 0 < crossIm α β) :
    0 < ∫ t in (0 : ℝ)..1, crossIm α β / Complex.normSq (t • α + β) := by
  have hc : crossIm α β ≠ 0 := ne_of_gt hcpos
  rw [integral_crossIm_div_normSq hc]
  rw [sub_pos]
  apply Real.arctan_strictMono
  have hP : 0 < Complex.normSq α := normSq_alpha_pos hc
  rw [div_lt_div_iff_of_pos_right hcpos]
  linarith

/-- **Negative sign**: negative cross product gives a negative swept
angle. -/
theorem integral_crossIm_div_normSq_neg (hcneg : crossIm α β < 0) :
    (∫ t in (0 : ℝ)..1, crossIm α β / Complex.normSq (t • α + β)) < 0 := by
  have hc : crossIm α β ≠ 0 := ne_of_lt hcneg
  rw [integral_crossIm_div_normSq hc]
  rw [sub_neg]
  apply Real.arctan_strictMono
  have hP : 0 < Complex.normSq α := normSq_alpha_pos hc
  have hdiff : (Complex.normSq α * 1 + dotRe α β) / crossIm α β
      - (Complex.normSq α * 0 + dotRe α β) / crossIm α β
      = Complex.normSq α / crossIm α β := by
    field_simp
    ring
  have hneg : Complex.normSq α / crossIm α β < 0 :=
    div_neg_of_pos_of_neg hP hcneg
  linarith

end ArctanLinearIntegral

end JacobianChallenge

end
