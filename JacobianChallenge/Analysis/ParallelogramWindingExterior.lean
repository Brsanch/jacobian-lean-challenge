/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramCauchy
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Exterior winding: the parallelogram does not wind around separated
points

For `x` strictly separated from the four sides by a real-linear
functional — `Re((z − x)·c) > 0` for all side points `z` — the
parallelogram boundary integral of `(z − x)⁻¹` vanishes: the rotated
logarithm `z ↦ log ((z − x)·c)` is a primitive on the separating
half-plane (which never meets the branch cut, since the real part of the
argument is positive there), and the telescoping FTC
(`boundaryIntegral_eq_zero_of_primitive`) finishes.

Together with `boundaryIntegral_inv_sub_interior` (`±2πi` inside) this
gives the complete winding dichotomy the residue-side assembly needs:
each subtracted principal part `n·x̃/(z − x̃)` contributes `±2πi·n·x̃`
when `x̃` is interior and `0` when `x̃` is separated-exterior.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral Metric
open scoped Real

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-- **Exterior winding vanishes**: if a real-linear functional
`z ↦ Re((z − x)·c)` is strictly positive on all four sides, the boundary
integral of `(z − x)⁻¹` is zero. -/
theorem boundaryIntegral_inv_sub_exterior (x c : ℂ)
    (h₀ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((side₀ a ω₁ ω₂ t - x) * c).re)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((side₁ a ω₁ ω₂ t - x) * c).re)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((side₂ a ω₁ ω₂ t - x) * c).re)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, 0 < ((side₃ a ω₁ ω₂ t - x) * c).re) :
    boundaryIntegral a ω₁ ω₂ (fun z => (z - x)⁻¹) = 0 := by
  classical
  -- The separating half-plane.
  set S : Set ℂ := {z : ℂ | 0 < ((z - x) * c).re} with hS_def
  -- `c ≠ 0` (otherwise the functional is identically zero).
  have hc : c ≠ 0 := by
    intro h0
    have := h₀ 0 (left_mem_Icc.mpr (by norm_num))
    rw [h0] at this
    simp at this
  -- Points of `S` are distinct from `x`.
  have hSx : ∀ z ∈ S, z - x ≠ 0 := by
    intro z hz h0
    have hz' : 0 < ((z - x) * c).re := hz
    rw [h0, zero_mul] at hz'
    simp at hz'
  -- The rotated-log primitive on `S`.
  have hΦ : ∀ z ∈ S, HasDerivAt (fun w : ℂ => Complex.log ((w - x) * c))
      ((z - x)⁻¹) z := by
    intro z hz
    have hzS : 0 < ((z - x) * c).re := hz
    have hmem : (z - x) * c ∈ Complex.slitPlane := Or.inl hzS
    have hzc : (z - x) * c ≠ 0 :=
      mul_ne_zero (hSx z hz) hc
    -- Inner affine map and its derivative.
    have hinner : HasDerivAt (fun w : ℂ => (w - x) * c) c z := by
      have h := ((hasDerivAt_id z).sub_const x).mul_const c
      simpa using h
    -- Compose with `log`.
    have hcomp := hinner.clog hmem
    -- Simplify the derivative value.
    have hval : c / ((z - x) * c) = (z - x)⁻¹ := by
      rw [mul_comm, ← div_div, div_self hc, one_div]
    rw [hval] at hcomp
    exact hcomp
  -- Continuity of `(z − x)⁻¹` on `S`.
  have hfc : ContinuousOn (fun z : ℂ => (z - x)⁻¹) S := by
    apply ContinuousOn.inv₀
    · exact (continuous_id.sub continuous_const).continuousOn
    · exact fun z hz => hSx z hz
  exact boundaryIntegral_eq_zero_of_primitive a ω₁ ω₂ hΦ hfc h₀ h₁ h₂ h₃

end ParallelogramWinding

end JacobianChallenge

end
