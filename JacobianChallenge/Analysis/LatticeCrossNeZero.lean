/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.ParallelogramWindingEval
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # `ℝ`-independent periods have nonzero cross product

The last interface bridge for the piece-5 assembly
(`HANDOFF_TLDIVSUM.md`): the orientation hypothesis
`latticeCross ω₁ ω₂ ≠ 0` consumed by the whole parallelogram toolbox
follows from `ℝ`-linear independence of the periods — which the lattice
basis provides (`basisFin2OfL_realLinearIndependent`).

Contrapositive: if the cross product vanishes, the explicit coefficient
pair `(ω₂.im, −ω₁.im)` (or `(ω₂.re, −ω₁.re)` when both imaginary parts
vanish, or `(1, 0)` when `ω₁ = 0`) is a nontrivial vanishing
combination.

No `sorry`, no `axiom`. -/

noncomputable section

namespace JacobianChallenge

namespace ParallelogramWinding

/-- **Nonzero cross product from `ℝ`-independence**: if `![ω₁, ω₂]` is
`ℝ`-linearly independent in `ℂ`, then `latticeCross ω₁ ω₂ ≠ 0`. -/
theorem latticeCross_ne_zero_of_linearIndependent {ω₁ ω₂ : ℂ}
    (h : LinearIndependent ℝ (![ω₁, ω₂] : Fin 2 → ℂ)) :
    latticeCross ω₁ ω₂ ≠ 0 := by
  intro hD
  rw [LinearIndependent.pair_iff] at h
  rw [latticeCross] at hD
  by_cases h1 : ω₂.im = 0 ∧ ω₁.im = 0
  · obtain ⟨h2, h3⟩ := h1
    by_cases h4 : ω₂.re = 0 ∧ ω₁.re = 0
    · -- `ω₁ = 0`: the pair `(1, 0)` kills independence.
      have hcomb : (1 : ℝ) • ω₁ + (0 : ℝ) • ω₂ = 0 := by
        apply Complex.ext
        · simp [Complex.real_smul, h4.2]
        · simp [Complex.real_smul, h3]
      exact one_ne_zero (h 1 0 hcomb).1
    · -- both periods real: the pair `(ω₂.re, −ω₁.re)` vanishes.
      have hcomb : (ω₂.re : ℝ) • ω₁ + (-ω₁.re : ℝ) • ω₂ = 0 := by
        apply Complex.ext
        · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
            zero_mul, sub_zero]
          ring
        · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im,
            zero_mul, add_zero, h2, h3]
          ring
      obtain ⟨ha, hb⟩ := h _ _ hcomb
      rw [not_and_or] at h4
      rcases h4 with h4 | h4
      · exact h4 ha
      · exact h4 (neg_eq_zero.mp hb)
  · -- the generic pair `(ω₂.im, −ω₁.im)` vanishes by `hD`.
    have hcomb : (ω₂.im : ℝ) • ω₁ + (-ω₁.im : ℝ) • ω₂ = 0 := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
          zero_mul, sub_zero]
        linarith [hD]
      · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im,
          zero_mul, add_zero]
        ring
    obtain ⟨ha, hb⟩ := h _ _ hcomb
    rw [not_and_or] at h1
    rcases h1 with h1 | h1
    · exact h1 ha
    · exact h1 (neg_eq_zero.mp hb)

end ParallelogramWinding

end JacobianChallenge

end
