/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramCauchy

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # The pairing algebra: opposite-side cancellation by periodicity

Piece 1 of the forward-Abel contour argument (`HANDOFF_TLDIVSUM.md`):
for a doubly periodic `g` (with periods `ω₁, ω₂`), the parallelogram
boundary integral of the Abel integrand `z·g(z)` collapses by
opposite-side cancellation to the **period-weighted pair of one-sided
log-integrals**:

  `∮_{∂Π(a)} z·g(z) dz = ω₁·Δ_v − ω₂·Δ_h`

with `Δ_h = ∫₀¹ g(a + t·ω₁)·ω₁ dt` and `Δ_v = ∫₀¹ g(a + t·ω₂)·ω₂ dt`
(`boundaryIntegral_mul_eq_pairing`). The mechanism: the reversed top
side at parameter `1 − t` is the bottom side shifted by `ω₂`, where `g`
takes the same value, so the `z`-weights subtract to the constant
`−ω₂`; similarly for the right/left pair.

Combined with the winding engine (`Analysis/LogDerivWinding.lean`:
`Δ_h, Δ_v ∈ 2πi·ℤ` for `g = F′/F`) this gives `I(a) ∈ 2πi·(ℤω₁ + ℤω₂)`,
the lattice-membership half of the parallelogram residue computation.

No `sorry`, no `axiom`. -/

noncomputable section

open Set MeasureTheory intervalIntegral

namespace JacobianChallenge

namespace ParallelogramWinding

variable (a ω₁ ω₂ : ℂ)

/-- **The pairing algebra**: for doubly periodic `g` integrable along
the two generator sides, the boundary integral of `z·g(z)` is
`ω₁·Δ_v − ω₂·Δ_h`. -/
theorem boundaryIntegral_mul_eq_pairing {g : ℂ → ℂ}
    (hper₁ : ∀ z, g (z + ω₁) = g z)
    (hper₂ : ∀ z, g (z + ω₂) = g z)
    (hcH : ContinuousOn (fun t : ℝ => g (a + t • ω₁)) (Icc 0 1))
    (hcV : ContinuousOn (fun t : ℝ => g (a + t • ω₂)) (Icc 0 1)) :
    boundaryIntegral a ω₁ ω₂ (fun z => z * g z)
      = ω₁ * (∫ t in (0 : ℝ)..1, g (a + t • ω₂) * ω₂)
        - ω₂ * ∫ t in (0 : ℝ)..1, g (a + t • ω₁) * ω₁ := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- Continuity of the affine side paths (via `ofReal`, dodging the
  -- `ContinuousSMul ℝ ℂ` instance quirk).
  have haff₁ : Continuous (fun t : ℝ => a + t • ω₁) := by
    have heq : (fun t : ℝ => a + t • ω₁)
        = fun t : ℝ => a + (t : ℂ) * ω₁ := by
      funext t
      rw [Complex.real_smul]
    rw [heq]
    exact continuous_const.add (Complex.continuous_ofReal.mul
      continuous_const)
  have haff₂ : Continuous (fun t : ℝ => a + t • ω₂) := by
    have heq : (fun t : ℝ => a + t • ω₂)
        = fun t : ℝ => a + (t : ℂ) * ω₂ := by
      funext t
      rw [Complex.real_smul]
    rw [heq]
    exact continuous_const.add (Complex.continuous_ofReal.mul
      continuous_const)
  -- Integrability of the four weighted integrands.
  have hint₀ : IntervalIntegrable
      (fun t : ℝ => (a + t • ω₁) * g (a + t • ω₁) * ω₁) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    exact (haff₁.continuousOn.mul hcH).mul continuousOn_const
  have hint₀' : IntervalIntegrable
      (fun t : ℝ => (a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    exact ((haff₁.add continuous_const).continuousOn.mul hcH).mul
      continuousOn_const
  have hint₃ : IntervalIntegrable
      (fun t : ℝ => (a + t • ω₂) * g (a + t • ω₂) * ω₂) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    exact (haff₂.continuousOn.mul hcV).mul continuousOn_const
  have hint₃' : IntervalIntegrable
      (fun t : ℝ => (a + t • ω₂ + ω₁) * g (a + t • ω₂) * ω₂)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    exact ((haff₂.add continuous_const).continuousOn.mul hcV).mul
      continuousOn_const
  -- Side 0: raw form.
  have e₀ : (∫ t in (0 : ℝ)..1,
        side₀ a ω₁ ω₂ t * g (side₀ a ω₁ ω₂ t) * ω₁)
      = ∫ t in (0 : ℝ)..1, (a + t • ω₁) * g (a + t • ω₁) * ω₁ := by
    apply integral_congr
    intro t _
    show side₀ a ω₁ ω₂ t * g (side₀ a ω₁ ω₂ t) * ω₁
      = (a + t • ω₁) * g (a + t • ω₁) * ω₁
    rw [side₀]
  -- Side 1: the left path shifted by the period `ω₁`.
  have e₁ : (∫ t in (0 : ℝ)..1,
        side₁ a ω₁ ω₂ t * g (side₁ a ω₁ ω₂ t) * ω₂)
      = ∫ t in (0 : ℝ)..1, (a + t • ω₂ + ω₁) * g (a + t • ω₂) * ω₂ := by
    apply integral_congr
    intro t _
    show side₁ a ω₁ ω₂ t * g (side₁ a ω₁ ω₂ t) * ω₂
      = (a + t • ω₂ + ω₁) * g (a + t • ω₂) * ω₂
    have hpt : side₁ a ω₁ ω₂ t = a + t • ω₂ + ω₁ := by
      rw [side₁]
      module
    rw [hpt, hper₁ (a + t • ω₂)]
  -- Side 2 reversed: at parameter `1 − t` it is side 0 shifted by the
  -- period `ω₂`.
  have e₂ : (∫ t in (0 : ℝ)..1,
        side₂ a ω₁ ω₂ t * g (side₂ a ω₁ ω₂ t) * (-ω₁))
      = ∫ t in (0 : ℝ)..1,
          -((a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁) := by
    calc (∫ t in (0 : ℝ)..1,
          side₂ a ω₁ ω₂ t * g (side₂ a ω₁ ω₂ t) * (-ω₁))
        = ∫ t in (1 - (1 : ℝ))..(1 - (0 : ℝ)),
            side₂ a ω₁ ω₂ t * g (side₂ a ω₁ ω₂ t) * (-ω₁) := by
          norm_num
      _ = ∫ t in (0 : ℝ)..1,
            side₂ a ω₁ ω₂ (1 - t) * g (side₂ a ω₁ ω₂ (1 - t)) * (-ω₁) :=
          (intervalIntegral.integral_comp_sub_left
            (f := fun t => side₂ a ω₁ ω₂ t * g (side₂ a ω₁ ω₂ t) * (-ω₁))
            1).symm
      _ = ∫ t in (0 : ℝ)..1,
            -((a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁) := by
          apply integral_congr
          intro t _
          show side₂ a ω₁ ω₂ (1 - t) * g (side₂ a ω₁ ω₂ (1 - t)) * (-ω₁)
            = -((a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁)
          have hpt : side₂ a ω₁ ω₂ (1 - t) = a + t • ω₁ + ω₂ := by
            rw [side₂]
            module
          rw [hpt, hper₂ (a + t • ω₁)]
          ring
  -- Side 3 reversed: at parameter `1 − t` it is the raw vertical path.
  have e₃ : (∫ t in (0 : ℝ)..1,
        side₃ a ω₁ ω₂ t * g (side₃ a ω₁ ω₂ t) * (-ω₂))
      = ∫ t in (0 : ℝ)..1,
          -((a + t • ω₂) * g (a + t • ω₂) * ω₂) := by
    calc (∫ t in (0 : ℝ)..1,
          side₃ a ω₁ ω₂ t * g (side₃ a ω₁ ω₂ t) * (-ω₂))
        = ∫ t in (1 - (1 : ℝ))..(1 - (0 : ℝ)),
            side₃ a ω₁ ω₂ t * g (side₃ a ω₁ ω₂ t) * (-ω₂) := by
          norm_num
      _ = ∫ t in (0 : ℝ)..1,
            side₃ a ω₁ ω₂ (1 - t) * g (side₃ a ω₁ ω₂ (1 - t)) * (-ω₂) :=
          (intervalIntegral.integral_comp_sub_left
            (f := fun t => side₃ a ω₁ ω₂ t * g (side₃ a ω₁ ω₂ t) * (-ω₂))
            1).symm
      _ = ∫ t in (0 : ℝ)..1,
            -((a + t • ω₂) * g (a + t • ω₂) * ω₂) := by
          apply integral_congr
          intro t _
          show side₃ a ω₁ ω₂ (1 - t) * g (side₃ a ω₁ ω₂ (1 - t)) * (-ω₂)
            = -((a + t • ω₂) * g (a + t • ω₂) * ω₂)
          have hpt : side₃ a ω₁ ω₂ (1 - t) = a + t • ω₂ := by
            rw [side₃]
            module
          rw [hpt]
          ring
  -- Concrete instances of the integral algebra (term-mode, dodging
  -- higher-order rewrite-pattern failures).
  have hneg₂ : (∫ t in (0 : ℝ)..1,
        -((a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁))
      = -∫ t in (0 : ℝ)..1, (a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁ :=
    intervalIntegral.integral_neg
  have hneg₃ : (∫ t in (0 : ℝ)..1,
        -((a + t • ω₂) * g (a + t • ω₂) * ω₂))
      = -∫ t in (0 : ℝ)..1, (a + t • ω₂) * g (a + t • ω₂) * ω₂ :=
    intervalIntegral.integral_neg
  have hcm₀ : (∫ t in (0 : ℝ)..1, ω₂ * (g (a + t • ω₁) * ω₁))
      = ω₂ * ∫ t in (0 : ℝ)..1, g (a + t • ω₁) * ω₁ :=
    intervalIntegral.integral_const_mul ω₂ (fun t => g (a + t • ω₁) * ω₁)
  have hcm₁ : (∫ t in (0 : ℝ)..1, ω₁ * (g (a + t • ω₂) * ω₂))
      = ω₁ * ∫ t in (0 : ℝ)..1, g (a + t • ω₂) * ω₂ :=
    intervalIntegral.integral_const_mul ω₁ (fun t => g (a + t • ω₂) * ω₂)
  -- The two pairs collapse to constant-weight integrals.
  have hpair₀ : (∫ t in (0 : ℝ)..1, (a + t • ω₁) * g (a + t • ω₁) * ω₁)
        - ∫ t in (0 : ℝ)..1, (a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁
      = -(ω₂ * ∫ t in (0 : ℝ)..1, g (a + t • ω₁) * ω₁) := by
    rw [← intervalIntegral.integral_sub hint₀ hint₀', ← hcm₀]
    have hsub : (∫ t in (0 : ℝ)..1,
          ((a + t • ω₁) * g (a + t • ω₁) * ω₁
            - (a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁))
        = ∫ t in (0 : ℝ)..1, -(ω₂ * (g (a + t • ω₁) * ω₁)) := by
      apply integral_congr
      intro t _
      show (a + t • ω₁) * g (a + t • ω₁) * ω₁
          - (a + t • ω₁ + ω₂) * g (a + t • ω₁) * ω₁
        = -(ω₂ * (g (a + t • ω₁) * ω₁))
      ring
    rw [hsub]
    exact intervalIntegral.integral_neg
  have hpair₁ : (∫ t in (0 : ℝ)..1,
        (a + t • ω₂ + ω₁) * g (a + t • ω₂) * ω₂)
        - ∫ t in (0 : ℝ)..1, (a + t • ω₂) * g (a + t • ω₂) * ω₂
      = ω₁ * ∫ t in (0 : ℝ)..1, g (a + t • ω₂) * ω₂ := by
    rw [← intervalIntegral.integral_sub hint₃' hint₃, ← hcm₁]
    apply integral_congr
    intro t _
    show (a + t • ω₂ + ω₁) * g (a + t • ω₂) * ω₂
        - (a + t • ω₂) * g (a + t • ω₂) * ω₂
      = ω₁ * (g (a + t • ω₂) * ω₂)
    ring
  -- Assemble.
  simp only [boundaryIntegral]
  rw [e₀, e₁, e₂, e₃, hneg₂, hneg₃]
  linear_combination hpair₀ + hpair₁

end ParallelogramWinding

end JacobianChallenge

end
