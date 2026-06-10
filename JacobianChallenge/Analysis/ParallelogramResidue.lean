/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramCauchy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # The parallelogram residue formula (subtracted form)

The residue side of the forward-Abel contour argument
(`HANDOFF_TLDIVSUM.md`, piece 3, items (ii)–(iii)): if on a ball
containing the four sides of `∂Π(a; ω₁, ω₂)` a function decomposes as

  `f z = H z + ∑ x ∈ P, coeff x / (z − x)`

with `H` differentiable on the ball and the finitely many poles `P` off
the boundary, then

  `∮_{∂Π} f = ∑ x ∈ P, coeff x · ∮_{∂Π} (z − x)⁻¹`.

The analytic part contributes nothing (`boundaryIntegral_eq_zero_of_differentiableOn_ball`,
the disk Cauchy theorem via mathlib's Morera machinery), and the
boundary integral is linear over the finite principal-part sum. Combined
with the winding dichotomy — `±2πi` at interior points
(`boundaryIntegral_inv_sub_interior`) and `0` at separated-exterior
points (`boundaryIntegral_inv_sub_exterior`) — this is the parallelogram
residue theorem the forward-Abel argument consumes.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral Metric

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-- **Per-segment decomposition**: along a continuous path `σ` staying in
the ball and avoiding the poles, the integral of `f·v` splits into the
analytic part plus the weighted winding-kernel integrals. -/
lemma segment_integral_decomp {f H : ℂ → ℂ} {c : ℂ} {R : ℝ}
    {P : Finset ℂ} {coeff : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball c R))
    (hdecomp : ∀ z ∈ ball c R, z ∉ (P : Set ℂ) →
      f z = H z + ∑ x ∈ P, coeff x / (z - x))
    {σ : ℝ → ℂ} (hσ : Continuous σ) (v : ℂ)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ ball c R)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ P, σ t ≠ x) :
    (∫ t in (0 : ℝ)..1, f (σ t) * v)
      = (∫ t in (0 : ℝ)..1, H (σ t) * v)
        + ∑ x ∈ P, coeff x * ∫ t in (0 : ℝ)..1, (σ t - x)⁻¹ * v := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- Pointwise decomposition of the integrand on the segment.
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1,
      f (σ t) * v
        = H (σ t) * v + ∑ x ∈ P, coeff x * ((σ t - x)⁻¹ * v) := by
    intro t ht
    have hP : σ t ∉ (P : Set ℂ) := fun hmem' => havoid t ht (σ t) hmem' rfl
    rw [hdecomp (σ t) (hmem t ht) hP, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [div_eq_mul_inv, mul_assoc]
  -- Integrability of the analytic part along the segment.
  have hHint : IntervalIntegrable (fun t => H (σ t) * v) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    exact (hH.continuousOn.comp hσ.continuousOn
      (fun t ht => hmem t ht)).mul continuousOn_const
  -- Integrability of each principal-part summand.
  have hPint : ∀ x ∈ P, IntervalIntegrable
      (fun t => coeff x * ((σ t - x)⁻¹ * v)) volume 0 1 := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul ?_ continuousOn_const
    apply ContinuousOn.inv₀ (hσ.continuousOn.sub continuousOn_const)
    intro t ht
    exact sub_ne_zero.mpr (havoid t ht x hx)
  -- Integrability of the principal-part sum.
  have hSint : IntervalIntegrable
      (fun t => ∑ x ∈ P, coeff x * ((σ t - x)⁻¹ * v)) volume 0 1 := by
    have h := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ))
      (b := (1 : ℝ)) P hPint
    convert h using 1
    ext t
    simp [Finset.sum_apply]
  calc (∫ t in (0 : ℝ)..1, f (σ t) * v)
      = ∫ t in (0 : ℝ)..1,
          (H (σ t) * v + ∑ x ∈ P, coeff x * ((σ t - x)⁻¹ * v)) := by
        apply integral_congr
        intro t ht
        rw [uIcc_of_le h01] at ht
        exact hpt t ht
    _ = (∫ t in (0 : ℝ)..1, H (σ t) * v)
          + ∫ t in (0 : ℝ)..1, ∑ x ∈ P, coeff x * ((σ t - x)⁻¹ * v) :=
        integral_add hHint hSint
    _ = (∫ t in (0 : ℝ)..1, H (σ t) * v)
          + ∑ x ∈ P, ∫ t in (0 : ℝ)..1, coeff x * ((σ t - x)⁻¹ * v) := by
        rw [integral_finset_sum hPint]
    _ = (∫ t in (0 : ℝ)..1, H (σ t) * v)
          + ∑ x ∈ P, coeff x * ∫ t in (0 : ℝ)..1, (σ t - x)⁻¹ * v := by
        congr 1
        exact Finset.sum_congr rfl fun x hx => integral_const_mul _ _

/-- **The parallelogram residue formula (subtracted form)**: if
`f = H + ∑ x ∈ P, coeff x / (z − x)` on a ball containing the four sides
with `H` differentiable on the ball and the poles off the boundary, the
boundary integral of `f` is the coefficient-weighted sum of the winding
integrals `∮ (z − x)⁻¹`. -/
theorem boundaryIntegral_eq_sum_winding {f H : ℂ → ℂ} {c : ℂ} {R : ℝ}
    {P : Finset ℂ} {coeff : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball c R))
    (hdecomp : ∀ z ∈ ball c R, z ∉ (P : Set ℂ) →
      f z = H z + ∑ x ∈ P, coeff x / (z - x))
    (hmem₀ : ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t ∈ ball c R)
    (hmem₁ : ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t ∈ ball c R)
    (hmem₂ : ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t ∈ ball c R)
    (hmem₃ : ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t ∈ ball c R)
    (havoid₀ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ P, side₀ a ω₁ ω₂ t ≠ x)
    (havoid₁ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ P, side₁ a ω₁ ω₂ t ≠ x)
    (havoid₂ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ P, side₂ a ω₁ ω₂ t ≠ x)
    (havoid₃ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ P, side₃ a ω₁ ω₂ t ≠ x) :
    boundaryIntegral a ω₁ ω₂ f
      = ∑ x ∈ P, coeff x
          * boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹) := by
  -- The four per-side decompositions.
  have e₀ := segment_integral_decomp hH hdecomp
    (continuous_side₀ a ω₁ ω₂) ω₁ hmem₀ havoid₀
  have e₁ := segment_integral_decomp hH hdecomp
    (continuous_side₁ a ω₁ ω₂) ω₂ hmem₁ havoid₁
  have e₂ := segment_integral_decomp hH hdecomp
    (continuous_side₂ a ω₁ ω₂) (-ω₁) hmem₂ havoid₂
  have e₃ := segment_integral_decomp hH hdecomp
    (continuous_side₃ a ω₁ ω₂) (-ω₂) hmem₃ havoid₃
  -- The analytic part contributes nothing (disk Cauchy).
  have hH0 : boundaryIntegral a ω₁ ω₂ H = 0 :=
    boundaryIntegral_eq_zero_of_differentiableOn_ball a ω₁ ω₂ hH
      hmem₀ hmem₁ hmem₂ hmem₃
  -- Split the winding boundary integrals on the right into their four
  -- side integrals.
  have hT : (∑ x ∈ P, coeff x
        * boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹))
      = (∑ x ∈ P, coeff x
            * ∫ t in (0 : ℝ)..1, (side₀ a ω₁ ω₂ t - x)⁻¹ * ω₁)
        + (∑ x ∈ P, coeff x
            * ∫ t in (0 : ℝ)..1, (side₁ a ω₁ ω₂ t - x)⁻¹ * ω₂)
        + (∑ x ∈ P, coeff x
            * ∫ t in (0 : ℝ)..1, (side₂ a ω₁ ω₂ t - x)⁻¹ * (-ω₁))
        + (∑ x ∈ P, coeff x
            * ∫ t in (0 : ℝ)..1, (side₃ a ω₁ ω₂ t - x)⁻¹ * (-ω₂)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [boundaryIntegral]
    ring
  rw [hT, boundaryIntegral, e₀, e₁, e₂, e₃]
  rw [boundaryIntegral] at hH0
  linear_combination hH0
end ParallelogramWinding

end JacobianChallenge

end
