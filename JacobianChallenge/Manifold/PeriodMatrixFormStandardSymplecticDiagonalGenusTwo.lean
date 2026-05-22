/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticDiagonalReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Genus-2 diagonal closed form (symbolic `g`)

Lifts `iPeriodMatrixForm_standardSymplectic_two_diagonal{_re,_im}`
from literal `Fin 4 / Fin 2` to symbolic `{g : ℕ}` with `h_g : g = 2`
via `subst h_g`. The closed form is expressed in terms of cycle
indices `k₀, k₁, k₂, k₃ : Fin (2 * g)` characterized by their
natural-number values 0, 1, 2, 3, and an arbitrary `i : Fin g`.

## What ships

* `iPeriodMatrixForm_standardSymplectic_diagonal_genus_two` — symbolic
  closed form (real number cast).
* `iPeriodMatrixForm_standardSymplectic_diagonal_genus_two_im` — `.im = 0`.
* `iPeriodMatrixForm_standardSymplectic_diagonal_genus_two_re` — `.re`
  closed form.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Symbolic-`g` closed form for the diagonal of `i • periodMatrixForm pm
(standardSymplectic g)` at `g = 2`.** -/
theorem iPeriodMatrixForm_standardSymplectic_diagonal_genus_two
    {g : ℕ} (h_g : g = 2)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i : Fin g) (k₀ k₁ k₂ k₃ : Fin (2 * g))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (h_k₂ : k₂.val = 2) (h_k₃ : k₃.val = 3) :
    ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic g)) i i
      = ((2 * ((star (pm k₀ i) * pm k₂ i).im
              + (star (pm k₁ i) * pm k₃ i).im) : ℝ) : ℂ) := by
  subst h_g
  -- After subst, g = 2; types are literal Fin 4 / Fin 2.
  have hk₀ : k₀ = (0 : Fin 4) := Fin.ext h_k₀
  have hk₁ : k₁ = (1 : Fin 4) := Fin.ext h_k₁
  have hk₂ : k₂ = (2 : Fin 4) := Fin.ext h_k₂
  have hk₃ : k₃ = (3 : Fin 4) := Fin.ext h_k₃
  rw [hk₀, hk₁, hk₂, hk₃]
  exact iPeriodMatrixForm_standardSymplectic_two_diagonal pm i

/-- **Imaginary part of the diagonal at `g = 2` (symbolic).** -/
theorem iPeriodMatrixForm_standardSymplectic_diagonal_genus_two_im
    {g : ℕ} (h_g : g = 2)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ) (i : Fin g) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic g)) i i).im = 0 := by
  subst h_g
  exact iPeriodMatrixForm_standardSymplectic_two_diagonal_im pm i

/-- **Real part of the diagonal at `g = 2` (symbolic).** -/
theorem iPeriodMatrixForm_standardSymplectic_diagonal_genus_two_re
    {g : ℕ} (h_g : g = 2)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i : Fin g) (k₀ k₁ k₂ k₃ : Fin (2 * g))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (h_k₂ : k₂.val = 2) (h_k₃ : k₃.val = 3) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic g)) i i).re
      = 2 * ((star (pm k₀ i) * pm k₂ i).im
            + (star (pm k₁ i) * pm k₃ i).im) := by
  subst h_g
  have hk₀ : k₀ = (0 : Fin 4) := Fin.ext h_k₀
  have hk₁ : k₁ = (1 : Fin 4) := Fin.ext h_k₁
  have hk₂ : k₂ = (2 : Fin 4) := Fin.ext h_k₂
  have hk₃ : k₃ = (3 : Fin 4) := Fin.ext h_k₃
  rw [hk₀, hk₁, hk₂, hk₃]
  exact iPeriodMatrixForm_standardSymplectic_two_diagonal_re pm i

end JacobianChallenge

end
