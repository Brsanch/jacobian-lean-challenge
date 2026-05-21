/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian

set_option linter.unusedSectionVars false

/-! # Matrix positivity at genus 1 reduces to scalar diagonal positivity (chip 19g)

For any complex `g × g` matrix `M`, the **positivity conjunct** of
Riemann's second bilinear relation,

  `∀ x ≠ 0, (star x ⬝ᵥ (M *ᵥ x)).im = 0 ∧ 0 < (star x ⬝ᵥ (M *ᵥ x)).re`,

is equivalent at `g = 1` to a **single scalar condition** on the
diagonal: the unique entry `M i₀ i₀` is a positive real (zero
imaginary part, strictly positive real part).

This is because at `g = 1`, the index `Fin g` is a `Subsingleton`, so
the quadratic form `star x ⬝ᵥ (M *ᵥ x)` collapses to
`M i₀ i₀ · |x i₀|²` — a positive-real scalar times the diagonal entry.

## What this file ships

* `riemannBilinearMatrixPos_of_diagonal_pos_genus_one` — the reduction.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

universe u

/-- **Genus-1 matrix positivity from scalar diagonal positivity.**
For any complex `g × g` matrix `M` with `g = 1` (so `Fin g` is a
subsingleton), the positivity conjunct of the second bilinear relation
holds iff each diagonal entry of `M` is a positive real. -/
theorem riemannBilinearMatrixPos_of_diagonal_pos_genus_one
    {g : ℕ} (h_g : g = 1)
    (M : Matrix (Fin g) (Fin g) ℂ)
    (h_diag_im : ∀ i, (M i i).im = 0)
    (h_diag_re : ∀ i, 0 < (M i i).re) :
    ∀ x : Fin g → ℂ, x ≠ 0 →
        (star x ⬝ᵥ (M *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ (M *ᵥ x)).re := by
  haveI hsub : Subsingleton (Fin g) := by
    rw [h_g]; infer_instance
  haveI hne : Nonempty (Fin g) := by
    rw [h_g]; exact ⟨0⟩
  intro x hx
  obtain ⟨i₀⟩ := hne
  -- M *ᵥ x at any i: collapse the sum over j to j = i₀.
  have hM_apply : ∀ i, (M *ᵥ x) i = M i i₀ * x i₀ := by
    intro i
    change (∑ j, M i j * x j) = M i i₀ * x i₀
    rw [Finset.sum_eq_single i₀]
    · intros j _ hj; exact absurd (Subsingleton.elim j i₀) hj
    · intro h_not_mem; exact absurd (Finset.mem_univ i₀) h_not_mem
  -- Now compute star x ⬝ᵥ (M *ᵥ x).
  -- = ∑ i, star (x i) * (M *ᵥ x) i
  -- = star (x i₀) * (M i₀ i₀ * x i₀)  (Subsingleton)
  -- = M i₀ i₀ * (x i₀ * star (x i₀))
  -- = M i₀ i₀ * normSq (x i₀)  (where normSq is coerced to ℂ).
  have h_dot : star x ⬝ᵥ (M *ᵥ x)
      = M i₀ i₀ * (Complex.normSq (x i₀) : ℂ) := by
    change (∑ i, star (x i) * (M *ᵥ x) i) = M i₀ i₀ * (Complex.normSq (x i₀) : ℂ)
    rw [Finset.sum_eq_single i₀]
    · rw [hM_apply i₀]
      have h_xstar : x i₀ * star (x i₀) = (Complex.normSq (x i₀) : ℂ) :=
        Complex.mul_conj _
      rw [show (star (x i₀) * (M i₀ i₀ * x i₀))
            = M i₀ i₀ * (x i₀ * star (x i₀)) from by ring, h_xstar]
    · intros j _ hj; exact absurd (Subsingleton.elim j i₀) hj
    · intro h_not_mem; exact absurd (Finset.mem_univ i₀) h_not_mem
  rw [h_dot]
  -- x i₀ ≠ 0 (since x ≠ 0 and Fin g is subsingleton).
  have hx_i0_ne : x i₀ ≠ 0 := by
    intro h
    apply hx
    funext i
    rw [Subsingleton.elim i i₀]
    exact h
  have h_normSq_pos : 0 < Complex.normSq (x i₀) := Complex.normSq_pos.mpr hx_i0_ne
  -- Now: (M i₀ i₀ * (normSq : ℂ)).im = (M i₀ i₀).im * 0 + ... = 0;
  --      (M i₀ i₀ * (normSq : ℂ)).re = (M i₀ i₀).re * normSq - (M i₀ i₀).im * 0 > 0.
  refine ⟨?_, ?_⟩
  · -- im = 0
    rw [Complex.mul_im, h_diag_im i₀, zero_mul, Complex.ofReal_im, mul_zero, add_zero]
  · -- 0 < re
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos (h_diag_re i₀) h_normSq_pos

end JacobianChallenge

end
