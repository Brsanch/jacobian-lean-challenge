/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticTwo

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `i • periodMatrixForm pm (standardSymplectic 2)` diagonal is real

At `g = 2`, the diagonal entries of `i • periodMatrixForm pm
(standardSymplectic 2)` are real numbers:

  `(i • M)_{i, i} = (2 · (Im(star pm_{0,i} · pm_{2,i}) +
                            Im(star pm_{1,i} · pm_{3,i})) : ℂ)`.

(Each summand `2 · Im(star pm_k · pm_{k+g})` is the same shape as the
genus-1 diagonal closed form from chip 19j, summed over `k = 0, 1`.)

## What ships

* `iPeriodMatrixForm_standardSymplectic_two_diagonal` — closed form
  of the diagonal entry as a real number cast to ℂ.
* `iPeriodMatrixForm_standardSymplectic_two_diagonal_im` —
  `(diagonal).im = 0`.
* `iPeriodMatrixForm_standardSymplectic_two_diagonal_re` — closed
  form for `(diagonal).re`.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Diagonal entry of `i • periodMatrixForm pm (standardSymplectic 2)`
is a real number.** -/
theorem iPeriodMatrixForm_standardSymplectic_two_diagonal
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (i : Fin 2) :
    ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) i i
      = ((2 * ((star (pm 0 i) * pm 2 i).im
              + (star (pm 1 i) * pm 3 i).im) : ℝ) : ℂ) := by
  rw [Matrix.smul_apply, periodMatrixForm_standardSymplectic_two_apply]
  -- Let a = pm 0 i, b = pm 1 i, c = pm 2 i, d = pm 3 i.
  -- Goal: I · (a · star c + b · star d - c · star a - d · star b)
  --     = (2 · (Im(star a · c) + Im(star b · d)) : ℂ).
  set a := pm 0 i
  set b := pm 1 i
  set c := pm 2 i
  set d := pm 3 i
  show Complex.I • (a * star c + b * star d - c * star a - d * star b)
      = ((2 * ((star a * c).im + (star b * d).im) : ℝ) : ℂ)
  change Complex.I * (a * star c + b * star d - c * star a - d * star b)
       = ((2 * ((star a * c).im + (star b * d).im) : ℝ) : ℂ)
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
               Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
               Complex.ofReal_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
               Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring

/-- **Imaginary part of the diagonal at `g = 2` is zero.** -/
theorem iPeriodMatrixForm_standardSymplectic_two_diagonal_im
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (i : Fin 2) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) i i).im = 0 := by
  rw [iPeriodMatrixForm_standardSymplectic_two_diagonal]
  exact Complex.ofReal_im _

/-- **Real part of the diagonal at `g = 2` is the sum of two
period-orientation scalars.** -/
theorem iPeriodMatrixForm_standardSymplectic_two_diagonal_re
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (i : Fin 2) :
    (((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) i i).re
      = 2 * ((star (pm 0 i) * pm 2 i).im + (star (pm 1 i) * pm 3 i).im) := by
  rw [iPeriodMatrixForm_standardSymplectic_two_diagonal]
  exact Complex.ofReal_re _

end JacobianChallenge

end
