/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramWinding
import Mathlib.Analysis.Complex.HasPrimitives

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Parallelogram Cauchy theorem via primitives

The vanishing half of the parallelogram residue calculus
(`HANDOFF_TLDIVSUM.md`, piece 3): the boundary integral over
`∂Π(a; ω₁, ω₂)` of any function with a primitive on a set containing the
four sides is zero (per-side FTC + corner telescoping), and hence — via
mathlib's Morera machinery (`DifferentiableOn.isExactOn_ball`) — the
boundary integral of a function **differentiable on a ball containing
the four sides** is zero.

The disk case is all the Cauchy theory the forward-Abel contour argument
needs: the principal-part-corrected integrand is differentiable on a
large disk around the parallelogram after removable-singularity
extension.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral Metric
open scoped Real

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-! ## Side endpoints and continuity -/

@[simp] lemma side₀_zero : side₀ a ω₁ ω₂ 0 = a := by
  rw [side₀]; module

@[simp] lemma side₀_one : side₀ a ω₁ ω₂ 1 = a + ω₁ := by
  rw [side₀]; module

@[simp] lemma side₁_zero : side₁ a ω₁ ω₂ 0 = a + ω₁ := by
  rw [side₁]; module

@[simp] lemma side₁_one : side₁ a ω₁ ω₂ 1 = a + ω₁ + ω₂ := by
  rw [side₁]; module

@[simp] lemma side₂_zero : side₂ a ω₁ ω₂ 0 = a + ω₁ + ω₂ := by
  rw [side₂]; module

@[simp] lemma side₂_one : side₂ a ω₁ ω₂ 1 = a + ω₂ := by
  rw [side₂]; module

@[simp] lemma side₃_zero : side₃ a ω₁ ω₂ 0 = a + ω₂ := by
  rw [side₃]; module

@[simp] lemma side₃_one : side₃ a ω₁ ω₂ 1 = a := by
  rw [side₃]; module

lemma continuous_side₀ : Continuous (side₀ a ω₁ ω₂) := by
  have heq : side₀ a ω₁ ω₂ = fun t : ℝ => a + (t : ℂ) * ω₁ := by
    funext t
    rw [side₀, Complex.real_smul]
  rw [heq]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

lemma continuous_side₁ : Continuous (side₁ a ω₁ ω₂) := by
  have heq : side₁ a ω₁ ω₂ = fun t : ℝ => (a + ω₁) + (t : ℂ) * ω₂ := by
    funext t
    rw [side₁, Complex.real_smul]
  rw [heq]
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

lemma continuous_side₂ : Continuous (side₂ a ω₁ ω₂) := by
  have heq : side₂ a ω₁ ω₂ = fun t : ℝ => (a + ω₁ + ω₂) - (t : ℂ) * ω₁ := by
    funext t
    rw [side₂, Complex.real_smul]
  rw [heq]
  exact continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)

lemma continuous_side₃ : Continuous (side₃ a ω₁ ω₂) := by
  have heq : side₃ a ω₁ ω₂ = fun t : ℝ => (a + ω₂) - (t : ℂ) * ω₂ := by
    funext t
    rw [side₃, Complex.real_smul]
  rw [heq]
  exact continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)

/-! ## FTC telescoping -/

/-- Per-side FTC: the integral along the affine segment `t ↦ p + t·v` of
a function with a primitive on a set containing the segment is the
primitive's endpoint difference. The chain rule is performed entirely
over `ℂ` and then composed with `ofReal`, avoiding the
`IsScalarTower ℝ ℂ ℂ` diamond. -/
lemma segment_integral_eq_sub {f Φ : ℂ → ℂ} {S : Set ℂ}
    (hΦ : ∀ z ∈ S, HasDerivAt Φ (f z) z)
    (hfc : ContinuousOn f S)
    (p v : ℂ)
    (hσS : ∀ t ∈ Icc (0 : ℝ) 1, p + (t : ℂ) * v ∈ S) :
    (∫ t in (0 : ℝ)..1, f (p + (t : ℂ) * v) * v) = Φ (p + v) - Φ p := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- The chain-rule derivative of `t ↦ Φ (p + t·v)`.
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Φ (p + (y : ℂ) * v))
        (f (p + (t : ℂ) * v) * v) t := by
    intro t ht
    rw [uIcc_of_le h01] at ht
    have haffine : HasDerivAt (fun w : ℂ => p + w * v) v ((t : ℝ) : ℂ) := by
      have h := ((hasDerivAt_id ((t : ℝ) : ℂ)).mul_const v).const_add p
      simpa using h
    have hcomp : HasDerivAt (fun w : ℂ => Φ (p + w * v))
        (f (p + (t : ℂ) * v) * v) ((t : ℝ) : ℂ) := by
      have h := (hΦ _ (hσS t ht)).comp ((t : ℝ) : ℂ) haffine
      exact h
    exact hcomp.comp_ofReal
  -- Integrability of the derivative.
  have hline : Continuous (fun t : ℝ => p + (t : ℂ) * v) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcont : ContinuousOn (fun t : ℝ => f (p + (t : ℂ) * v) * v)
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le h01]
    apply ContinuousOn.mul ?_ continuousOn_const
    exact hfc.comp hline.continuousOn (fun t ht => hσS t ht)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable)
  rw [hint]
  norm_num

/-- **Parallelogram FTC telescoping**: the boundary integral of a
function with a primitive on a set containing the four sides is zero. -/
theorem boundaryIntegral_eq_zero_of_primitive {f Φ : ℂ → ℂ} {S : Set ℂ}
    (hΦ : ∀ z ∈ S, HasDerivAt Φ (f z) z)
    (hfc : ContinuousOn f S)
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t ∈ S)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t ∈ S)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t ∈ S)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t ∈ S) :
    boundaryIntegral a ω₁ ω₂ f = 0 := by
  -- The four sides in `p + t·v` form.
  have hs₀ : ∀ t : ℝ, side₀ a ω₁ ω₂ t = a + (t : ℂ) * ω₁ := by
    intro t
    rw [side₀, Complex.real_smul]
  have hs₁ : ∀ t : ℝ, side₁ a ω₁ ω₂ t = (a + ω₁) + (t : ℂ) * ω₂ := by
    intro t
    rw [side₁, Complex.real_smul]
  have hs₂ : ∀ t : ℝ,
      side₂ a ω₁ ω₂ t = (a + ω₁ + ω₂) + (t : ℂ) * (-ω₁) := by
    intro t
    rw [side₂, Complex.real_smul]
    ring
  have hs₃ : ∀ t : ℝ, side₃ a ω₁ ω₂ t = (a + ω₂) + (t : ℂ) * (-ω₂) := by
    intro t
    rw [side₃, Complex.real_smul]
    ring
  -- Per-side endpoint differences.
  have e₀ := segment_integral_eq_sub hΦ hfc a ω₁
    (fun t ht => by rw [← hs₀ t]; exact h₀ t ht)
  have e₁ := segment_integral_eq_sub hΦ hfc (a + ω₁) ω₂
    (fun t ht => by rw [← hs₁ t]; exact h₁ t ht)
  have e₂ := segment_integral_eq_sub hΦ hfc (a + ω₁ + ω₂) (-ω₁)
    (fun t ht => by rw [← hs₂ t]; exact h₂ t ht)
  have e₃ := segment_integral_eq_sub hΦ hfc (a + ω₂) (-ω₂)
    (fun t ht => by rw [← hs₃ t]; exact h₃ t ht)
  -- Rewrite the boundary integral into segment form and telescope.
  have hbd : boundaryIntegral a ω₁ ω₂ f
      = (∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * ω₁) * ω₁)
        + (∫ t in (0 : ℝ)..1, f ((a + ω₁) + (t : ℂ) * ω₂) * ω₂)
        + (∫ t in (0 : ℝ)..1, f ((a + ω₁ + ω₂) + (t : ℂ) * (-ω₁)) * (-ω₁))
        + (∫ t in (0 : ℝ)..1, f ((a + ω₂) + (t : ℂ) * (-ω₂)) * (-ω₂)) := by
    have c₀ : (∫ t in (0 : ℝ)..1, f (side₀ a ω₁ ω₂ t) * ω₁)
        = ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * ω₁) * ω₁ :=
      integral_congr (fun t _ => by rw [hs₀ t])
    have c₁ : (∫ t in (0 : ℝ)..1, f (side₁ a ω₁ ω₂ t) * ω₂)
        = ∫ t in (0 : ℝ)..1, f ((a + ω₁) + (t : ℂ) * ω₂) * ω₂ :=
      integral_congr (fun t _ => by rw [hs₁ t])
    have c₂ : (∫ t in (0 : ℝ)..1, f (side₂ a ω₁ ω₂ t) * (-ω₁))
        = ∫ t in (0 : ℝ)..1, f ((a + ω₁ + ω₂) + (t : ℂ) * (-ω₁)) * (-ω₁) :=
      integral_congr (fun t _ => by rw [hs₂ t])
    have c₃ : (∫ t in (0 : ℝ)..1, f (side₃ a ω₁ ω₂ t) * (-ω₂))
        = ∫ t in (0 : ℝ)..1, f ((a + ω₂) + (t : ℂ) * (-ω₂)) * (-ω₂) :=
      integral_congr (fun t _ => by rw [hs₃ t])
    rw [boundaryIntegral, c₀, c₁, c₂, c₃]
  rw [hbd, e₀, e₁, e₂, e₃]
  have harg₂ : (a + ω₁ + ω₂) + (-ω₁) = a + ω₂ := by ring
  have harg₃ : (a + ω₂) + (-ω₂) = a := by ring
  rw [harg₂, harg₃]
  ring

/-- **Parallelogram Cauchy theorem (disk version)**: the boundary
integral of a function differentiable on a ball containing the four sides
is zero. -/
theorem boundaryIntegral_eq_zero_of_differentiableOn_ball
    {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R))
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, side₀ a ω₁ ω₂ t ∈ ball c R)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, side₁ a ω₁ ω₂ t ∈ ball c R)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, side₂ a ω₁ ω₂ t ∈ ball c R)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, side₃ a ω₁ ω₂ t ∈ ball c R) :
    boundaryIntegral a ω₁ ω₂ f = 0 := by
  obtain ⟨Φ, hΦ⟩ := hf.isExactOn_ball
  exact boundaryIntegral_eq_zero_of_primitive a ω₁ ω₂ hΦ hf.continuousOn
    h₀ h₁ h₂ h₃

end ParallelogramWinding

end JacobianChallenge

end
