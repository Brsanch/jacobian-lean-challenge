/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.LogDerivWinding

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # The parallelogram boundary integral and winding integrality

Defines the boundary contour integral over the parallelogram
`Π(a; ω₁, ω₂) = a + [0,1]·ω₁ + [0,1]·ω₂` (four affine sides, positively
ordered `bottom → right → top → left`), and proves **keystone-1** of
`HANDOFF_TLDIVSUM.md`:

* `parallelogram_winding_integrality` — for `x` off the boundary,
  `∮_{∂Π} (z − x)⁻¹ dz ∈ 2πi·ℤ`.

Proof: the exp-identity (`LogDerivWinding.exp_integral_logDeriv`)
applied to the four affine segments `t ↦ side_i(t) − x`; the product of
the endpoint quotients telescopes to `1` around the closed contour, so
the exponential of the total integral is `1`.

Remaining keystone halves (locally-constant in `x` + one explicit
evaluation `= 2πi`) are follow-up chips.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped Real

namespace JacobianChallenge

namespace ParallelogramWinding

/-! ## The four sides -/

/-- Bottom side `a + t·ω₁`. -/
def side₀ (a ω₁ ω₂ : ℂ) (t : ℝ) : ℂ := a + t • ω₁

/-- Right side `a + ω₁ + t·ω₂`. -/
def side₁ (a ω₁ ω₂ : ℂ) (t : ℝ) : ℂ := a + ω₁ + t • ω₂

/-- Top side (reversed) `a + ω₁ + ω₂ − t·ω₁`. -/
def side₂ (a ω₁ ω₂ : ℂ) (t : ℝ) : ℂ := a + ω₁ + ω₂ - t • ω₁

/-- Left side (reversed) `a + ω₂ − t·ω₂`. -/
def side₃ (a ω₁ ω₂ : ℂ) (t : ℝ) : ℂ := a + ω₂ - t • ω₂

/-- **The parallelogram boundary integral** of `f` over
`∂Π(a; ω₁, ω₂)`, as the sum of the four interval integrals
`∫ f(side(t))·side'(t) dt`. -/
def boundaryIntegral (a ω₁ ω₂ : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..1, f (side₀ a ω₁ ω₂ t) * ω₁)
    + (∫ t in (0 : ℝ)..1, f (side₁ a ω₁ ω₂ t) * ω₂)
    + (∫ t in (0 : ℝ)..1, f (side₂ a ω₁ ω₂ t) * (-ω₁))
    + (∫ t in (0 : ℝ)..1, f (side₃ a ω₁ ω₂ t) * (-ω₂))

/-! ## Derivatives of the sides -/

lemma hasDerivAt_side₀ (a ω₁ ω₂ : ℂ) (t : ℝ) :
    HasDerivAt (side₀ a ω₁ ω₂) ω₁ t := by
  have h := ((hasDerivAt_id t).smul_const ω₁).const_add a
  convert h using 1
  module

lemma hasDerivAt_side₁ (a ω₁ ω₂ : ℂ) (t : ℝ) :
    HasDerivAt (side₁ a ω₁ ω₂) ω₂ t := by
  have h := ((hasDerivAt_id t).smul_const ω₂).const_add (a + ω₁)
  convert h using 1
  module

lemma hasDerivAt_side₂ (a ω₁ ω₂ : ℂ) (t : ℝ) :
    HasDerivAt (side₂ a ω₁ ω₂) (-ω₁) t := by
  have h := ((hasDerivAt_id t).smul_const ω₁).const_sub (a + ω₁ + ω₂)
  convert h using 1
  module

lemma hasDerivAt_side₃ (a ω₁ ω₂ : ℂ) (t : ℝ) :
    HasDerivAt (side₃ a ω₁ ω₂) (-ω₂) t := by
  have h := ((hasDerivAt_id t).smul_const ω₂).const_sub (a + ω₂)
  convert h using 1
  module

/-! ## Keystone-1: winding integrality -/

/-- **Keystone-1 (`HANDOFF_TLDIVSUM.md`)**: for `x` off the four sides,
the parallelogram boundary integral of `(z − x)⁻¹` lies in `2πi·ℤ`. -/
theorem parallelogram_winding_integrality (a ω₁ ω₂ x : ℂ)
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t ≠ x)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t ≠ x)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t ≠ x)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t ≠ x) :
    ∃ k : ℤ, boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹)
      = k * (2 * Real.pi * Complex.I) := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- The four shifted segments and their exp-identities.
  -- Segment 0.
  have hd₀ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => side₀ a ω₁ ω₂ s - x) ω₁ t :=
    fun t _ => (hasDerivAt_side₀ a ω₁ ω₂ t).sub_const x
  have hne₀ : ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t - x ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (h₀ t ht)
  have he₀ := LogDerivWinding.exp_integral_logDeriv
    (φ := fun s => side₀ a ω₁ ω₂ s - x) (φ' := fun _ => ω₁)
    hd₀ continuousOn_const hne₀
  -- Segment 1.
  have hd₁ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => side₁ a ω₁ ω₂ s - x) ω₂ t :=
    fun t _ => (hasDerivAt_side₁ a ω₁ ω₂ t).sub_const x
  have hne₁ : ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t - x ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (h₁ t ht)
  have he₁ := LogDerivWinding.exp_integral_logDeriv
    (φ := fun s => side₁ a ω₁ ω₂ s - x) (φ' := fun _ => ω₂)
    hd₁ continuousOn_const hne₁
  -- Segment 2.
  have hd₂ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => side₂ a ω₁ ω₂ s - x) (-ω₁) t :=
    fun t _ => (hasDerivAt_side₂ a ω₁ ω₂ t).sub_const x
  have hne₂ : ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t - x ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (h₂ t ht)
  have he₂ := LogDerivWinding.exp_integral_logDeriv
    (φ := fun s => side₂ a ω₁ ω₂ s - x) (φ' := fun _ => -ω₁)
    hd₂ continuousOn_const hne₂
  -- Segment 3.
  have hd₃ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s => side₃ a ω₁ ω₂ s - x) (-ω₂) t :=
    fun t _ => (hasDerivAt_side₃ a ω₁ ω₂ t).sub_const x
  have hne₃ : ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t - x ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (h₃ t ht)
  have he₃ := LogDerivWinding.exp_integral_logDeriv
    (φ := fun s => side₃ a ω₁ ω₂ s - x) (φ' := fun _ => -ω₂)
    hd₃ continuousOn_const hne₃
  -- Identify the boundary integral with the sum of log-derivative
  -- integrals.
  have hint : boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹)
      = (∫ t in (0 : ℝ)..1, ω₁ / (side₀ a ω₁ ω₂ t - x))
        + (∫ t in (0 : ℝ)..1, ω₂ / (side₁ a ω₁ ω₂ t - x))
        + (∫ t in (0 : ℝ)..1, (-ω₁) / (side₂ a ω₁ ω₂ t - x))
        + (∫ t in (0 : ℝ)..1, (-ω₂) / (side₃ a ω₁ ω₂ t - x)) := by
    unfold boundaryIntegral
    congr 1
    · congr 1
      · congr 1
        · apply integral_congr
          intro t _
          show (side₀ a ω₁ ω₂ t - x)⁻¹ * ω₁ = ω₁ / (side₀ a ω₁ ω₂ t - x)
          rw [inv_mul_eq_div]
        · apply integral_congr
          intro t _
          show (side₁ a ω₁ ω₂ t - x)⁻¹ * ω₂ = ω₂ / (side₁ a ω₁ ω₂ t - x)
          rw [inv_mul_eq_div]
      · apply integral_congr
        intro t _
        show (side₂ a ω₁ ω₂ t - x)⁻¹ * (-ω₁) = (-ω₁) / (side₂ a ω₁ ω₂ t - x)
        rw [inv_mul_eq_div]
    · apply integral_congr
      intro t _
      show (side₃ a ω₁ ω₂ t - x)⁻¹ * (-ω₂) = (-ω₂) / (side₃ a ω₁ ω₂ t - x)
      rw [inv_mul_eq_div]
  -- Exponential of the total integral telescopes to 1.
  apply Complex.exp_eq_one_iff.mp
  rw [hint]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]
  rw [he₀, he₁, he₂, he₃]
  -- Endpoint values.
  have hv₀₀ : side₀ a ω₁ ω₂ 0 - x = a - x := by
    unfold side₀; module
  have hv₀₁ : side₀ a ω₁ ω₂ 1 - x = a + ω₁ - x := by
    unfold side₀; module
  have hv₁₀ : side₁ a ω₁ ω₂ 0 - x = a + ω₁ - x := by
    unfold side₁; module
  have hv₁₁ : side₁ a ω₁ ω₂ 1 - x = a + ω₁ + ω₂ - x := by
    unfold side₁; module
  have hv₂₀ : side₂ a ω₁ ω₂ 0 - x = a + ω₁ + ω₂ - x := by
    unfold side₂; module
  have hv₂₁ : side₂ a ω₁ ω₂ 1 - x = a + ω₂ - x := by
    unfold side₂; module
  have hv₃₀ : side₃ a ω₁ ω₂ 0 - x = a + ω₂ - x := by
    unfold side₃; module
  have hv₃₁ : side₃ a ω₁ ω₂ 1 - x = a - x := by
    unfold side₃; module
  beta_reduce
  rw [hv₀₀, hv₀₁, hv₁₀, hv₁₁, hv₂₀, hv₂₁, hv₃₀, hv₃₁]
  -- Nonvanishing of the four corner values.
  have hc₀ : a - x ≠ 0 := by
    rw [← hv₀₀]; exact hne₀ 0 (left_mem_Icc.mpr h01)
  have hc₁ : a + ω₁ - x ≠ 0 := by
    rw [← hv₁₀]; exact hne₁ 0 (left_mem_Icc.mpr h01)
  have hc₂ : a + ω₁ + ω₂ - x ≠ 0 := by
    rw [← hv₂₀]; exact hne₂ 0 (left_mem_Icc.mpr h01)
  have hc₃ : a + ω₂ - x ≠ 0 := by
    rw [← hv₃₀]; exact hne₃ 0 (left_mem_Icc.mpr h01)
  field_simp

end ParallelogramWinding

end JacobianChallenge

end
