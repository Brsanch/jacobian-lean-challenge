/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticOne

set_option linter.unusedSectionVars false

/-! # Symbolic-`g` transport of chip 19i (chip 19j)

Chip 19i proved the closed form for `periodMatrixForm pm (standardSymplectic 1)`
at literal `Fin 2 / Fin 1`. This file transports the result to symbolic
`{g : ℕ}` with `h_g : g = 1` via `subst h_g`. The closed form is
expressed in terms of two cycle indices `k₀, k₁ : Fin (2 * g)` characterized
by their natural-number values `.val = 0` and `.val = 1`, and the unique
basis-coordinate index `i₀ : Fin g`.

This is the most useful form for downstream consumers reasoning about
the genus-1 Riemann–Hodge content of a complex 1-manifold.

## What this file ships

* `periodMatrixForm_standardSymplectic_diagonal_genus_one` — symbolic
  closed form.
* `iPeriodMatrixForm_standardSymplectic_diagonal_genus_one` — closed
  form with the `i` factor (yields a real number).
* `iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_im` /`_re` —
  explicit im/re of the diagonal.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Symbolic-`g` closed form for `periodMatrixForm pm (standardSymplectic g)`
at `g = 1`.** Given a generic `pm : Matrix (Fin (2 * g)) (Fin g) ℂ`, the
diagonal entry at the unique basis index `i₀ : Fin g` equals
`pm k₀ i₀ · star (pm k₁ i₀) - pm k₁ i₀ · star (pm k₀ i₀)`, where
`k₀, k₁ : Fin (2 * g)` are the two cycle indices characterized by
`.val = 0` and `.val = 1`. -/
theorem periodMatrixForm_standardSymplectic_diagonal_genus_one
    {g : ℕ} (h_g : g = 1)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i₀ : Fin g) (k₀ k₁ : Fin (2 * g))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1) :
    (periodMatrixForm pm (standardSymplectic g)) i₀ i₀
      = pm k₀ i₀ * star (pm k₁ i₀) - pm k₁ i₀ * star (pm k₀ i₀) := by
  subst h_g
  -- After subst, g = 1; the types are literal Fin 2 / Fin 1.
  -- i₀ : Fin 1, so i₀ = 0 (Subsingleton).
  -- k₀ : Fin 2 with k₀.val = 0, so k₀ = 0.
  -- k₁ : Fin 2 with k₁.val = 1, so k₁ = 1.
  obtain rfl : i₀ = 0 := Subsingleton.elim _ _
  have hk₀_eq : k₀ = (0 : Fin 2) := Fin.ext h_k₀
  have hk₁_eq : k₁ = (1 : Fin 2) := Fin.ext h_k₁
  rw [hk₀_eq, hk₁_eq]
  exact periodMatrixForm_standardSymplectic_one_apply pm

/-- **The diagonal of `i • periodMatrixForm pm (standardSymplectic g)`
at `g = 1` is a real number.** Specifically equals
`(2 · Im(star (pm k₀ i₀) · pm k₁ i₀) : ℂ)`. -/
theorem iPeriodMatrixForm_standardSymplectic_diagonal_genus_one
    {g : ℕ} (h_g : g = 1)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i₀ : Fin g) (k₀ k₁ : Fin (2 * g))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1) :
    ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic g)) i₀ i₀
      = ((2 * (star (pm k₀ i₀) * pm k₁ i₀).im : ℝ) : ℂ) := by
  subst h_g
  obtain rfl : i₀ = 0 := Subsingleton.elim _ _
  have hk₀_eq : k₀ = (0 : Fin 2) := Fin.ext h_k₀
  have hk₁_eq : k₁ = (1 : Fin 2) := Fin.ext h_k₁
  rw [hk₀_eq, hk₁_eq]
  exact iPeriodMatrixForm_standardSymplectic_one_diagonal pm

/-- **Imaginary part of the diagonal is zero.** -/
theorem iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_im
    {g : ℕ} (h_g : g = 1)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i₀ : Fin g) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic g)) i₀ i₀).im = 0 := by
  subst h_g
  obtain rfl : i₀ = 0 := Subsingleton.elim _ _
  exact iPeriodMatrixForm_standardSymplectic_one_diagonal_im pm

/-- **Real part of the diagonal equals `2 · Im(star (pm k₀ i₀) · pm k₁ i₀)`.** -/
theorem iPeriodMatrixForm_standardSymplectic_diagonal_genus_one_re
    {g : ℕ} (h_g : g = 1)
    (pm : Matrix (Fin (2 * g)) (Fin g) ℂ)
    (i₀ : Fin g) (k₀ k₁ : Fin (2 * g))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic g)) i₀ i₀).re
      = 2 * (star (pm k₀ i₀) * pm k₁ i₀).im := by
  subst h_g
  obtain rfl : i₀ = 0 := Subsingleton.elim _ _
  have hk₀_eq : k₀ = (0 : Fin 2) := Fin.ext h_k₀
  have hk₁_eq : k₁ = (1 : Fin 2) := Fin.ext h_k₁
  rw [hk₀_eq, hk₁_eq]
  exact iPeriodMatrixForm_standardSymplectic_one_diagonal_re pm

end JacobianChallenge

end
