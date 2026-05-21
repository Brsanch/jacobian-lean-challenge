/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false

/-! # Closed form for `periodMatrixForm pm (standardSymplectic 1)` (chip 19i)

For `pm : Matrix (Fin 2) (Fin 1) ℂ` (a generic genus-1 period matrix
viewed at literal `Fin 2 × Fin 1` dimensions) and the standard
symplectic form `J := standardSymplectic 1 = [[0,1];[-1,0]]`, the
`Fin 1 × Fin 1` matrix `periodMatrixForm pm J` has the closed form

  `(periodMatrixForm pm J) 0 0 = pm 0 0 · star (pm 1 0) - pm 1 0 · star (pm 0 0)`.

Multiplying by `i`, the diagonal entry becomes a **purely real** number:

  `(i • periodMatrixForm pm J) 0 0 = (2 · Im(star (pm 0 0) · pm 1 0) : ℂ)`.

Its `.re` is `2 · Im(star (pm 0 0) · pm 1 0)` and its `.im = 0`. Hence
the "diagonal positivity" required by chip 19h reduces to the **lattice
orientation condition**

  `0 < Im(star (pm 0 0) · pm 1 0)`.

This is the standard "positive orientation" of the genus-1 (or torus)
period lattice.

## What this file ships

* `periodMatrixForm_standardSymplectic_one_apply` — closed form for the
  diagonal entry without the `i` factor.
* `iPeriodMatrixForm_standardSymplectic_one_diagonal` — closed form
  with the `i` factor, expressing the entry as a real number.
* `iPeriodMatrixForm_standardSymplectic_one_diagonal_im` — the entry
  has zero imaginary part.
* `iPeriodMatrixForm_standardSymplectic_one_diagonal_re` — the
  entry's real part equals `2 · Im(star (pm 0 0) · pm 1 0)`.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Closed form for the `(0,0)` entry of `periodMatrixForm pm J`
at `J := standardSymplectic 1`.** -/
theorem periodMatrixForm_standardSymplectic_one_apply
    (pm : Matrix (Fin 2) (Fin 1) ℂ) :
    (periodMatrixForm pm (standardSymplectic 1)) 0 0
      = pm 0 0 * star (pm 1 0) - pm 1 0 * star (pm 0 0) := by
  unfold periodMatrixForm
  -- Unfold the matrix product element-wise.
  rw [Matrix.mul_apply]
  -- Sum is over k : Fin 2 = {0, 1}.
  rw [Fin.sum_univ_two]
  -- Each term: (pmᵀ * J.map ↑) 0 k * (pm.map star) k 0
  rw [Matrix.mul_apply, Matrix.mul_apply]
  -- Inner sums over j : Fin 2.
  simp only [Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply]
  -- Substitute the standardSymplectic 1 values.
  -- J 0 0 = 0, J 0 1 = 1, J 1 0 = -1, J 1 1 = 0.
  have h00 : (standardSymplectic 1) 0 0 = 0 := by
    rw [standardSymplectic_top_right 1 0 0 (by decide)]; decide
  have h01 : (standardSymplectic 1) 0 1 = 1 := by
    rw [standardSymplectic_top_right 1 0 1 (by decide)]; decide
  have h10 : (standardSymplectic 1) 1 0 = -1 := by
    rw [standardSymplectic_bottom_left 1 1 0 (by decide)]; decide
  have h11 : (standardSymplectic 1) 1 1 = 0 := by
    rw [standardSymplectic_bottom_left 1 1 1 (by decide)]; decide
  rw [h00, h01, h10, h11]
  push_cast
  ring

/-- **The diagonal entry of `i • periodMatrixForm pm (standardSymplectic 1)`
is a real number.** Specifically `(2 · Im(star (pm 0 0) · pm 1 0) : ℂ)`. -/
theorem iPeriodMatrixForm_standardSymplectic_one_diagonal
    (pm : Matrix (Fin 2) (Fin 1) ℂ) :
    ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 1)) 0 0
      = ((2 * (star (pm 0 0) * pm 1 0).im : ℝ) : ℂ) := by
  rw [Matrix.smul_apply, periodMatrixForm_standardSymplectic_one_apply]
  -- Goal: I • (pm 0 0 * star (pm 1 0) - pm 1 0 * star (pm 0 0))
  --     = (2 * (star (pm 0 0) * pm 1 0).im : ℂ)
  -- Strategy: a := pm 0 0, b := pm 1 0. Then expr = i * (a * star b - b * star a).
  -- a * star b - b * star a = star(b * star a) ... no let's compute differently.
  -- Set z := star a * b. Then star z = a * star b.
  -- Want: i * (star z - z) = -i * (z - star z) = -i * (2i * Im z) = 2 * Im z.
  -- So a * star b - b * star a = star z - z = -(z - star z) = -2i * Im z.
  -- Hence i * (...) = i * (-2i * Im z) = 2 * Im z.
  set a := pm 0 0
  set b := pm 1 0
  show Complex.I • (a * star b - b * star a)
      = ((2 * (star a * b).im : ℝ) : ℂ)
  change Complex.I * (a * star b - b * star a) = ((2 * (star a * b).im : ℝ) : ℂ)
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
               Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
               Complex.I_re, Complex.I_im, Complex.ofReal_im,
               Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring

/-- **Imaginary part of the diagonal is zero.** -/
theorem iPeriodMatrixForm_standardSymplectic_one_diagonal_im
    (pm : Matrix (Fin 2) (Fin 1) ℂ) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 1)) 0 0).im = 0 := by
  rw [iPeriodMatrixForm_standardSymplectic_one_diagonal]
  exact Complex.ofReal_im _

/-- **Real part of the diagonal equals `2 · Im(star (pm 0 0) · pm 1 0)`.** -/
theorem iPeriodMatrixForm_standardSymplectic_one_diagonal_re
    (pm : Matrix (Fin 2) (Fin 1) ℂ) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 1)) 0 0).re
      = 2 * (star (pm 0 0) * pm 1 0).im := by
  rw [iPeriodMatrixForm_standardSymplectic_one_diagonal]
  exact Complex.ofReal_re _

end JacobianChallenge

end
