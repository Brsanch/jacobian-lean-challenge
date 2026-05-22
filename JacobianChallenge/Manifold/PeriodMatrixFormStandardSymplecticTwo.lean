/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Closed form for `periodMatrixForm pm (standardSymplectic 2)` at all 4 entries

For `pm : Matrix (Fin 4) (Fin 2) ℂ` (a generic genus-2 period matrix
at literal dimensions), the four entries of the `Fin 2 × Fin 2` matrix
`periodMatrixForm pm (standardSymplectic 2)` admit closed forms:

  `(M)_{i, j} = pm_{0, i} · star(pm_{2, j}) + pm_{1, i} · star(pm_{3, j})
              − pm_{2, i} · star(pm_{0, j}) − pm_{3, i} · star(pm_{1, j})`

(uniform across all 4 (i, j) pairs).

Generalises chip 19i (genus-1 (0, 0) entry) to genus 2.

## What ships

* `periodMatrixForm_standardSymplectic_two_apply` — closed form for the
  generic entry `(i, j)` at `g = 2`.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Closed form for the `(i, j)` entry of `periodMatrixForm pm
(standardSymplectic 2)`.** -/
theorem periodMatrixForm_standardSymplectic_two_apply
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (i j : Fin 2) :
    (periodMatrixForm pm (standardSymplectic 2)) i j
      = pm 0 i * star (pm 2 j) + pm 1 i * star (pm 3 j)
        - pm 2 i * star (pm 0 j) - pm 3 i * star (pm 1 j) := by
  unfold periodMatrixForm
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_four]
  rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply]
  -- Substitute standardSymplectic 2 values.
  -- J has 1 at (0,2), (1,3) and -1 at (2,0), (3,1); zero elsewhere.
  have h_00 : (standardSymplectic 2) 0 0 = 0 := by
    rw [standardSymplectic_top_right 2 0 0 (by decide)]; decide
  have h_01 : (standardSymplectic 2) 0 1 = 0 := by
    rw [standardSymplectic_top_right 2 0 1 (by decide)]; decide
  have h_02 : (standardSymplectic 2) 0 2 = 1 := by
    rw [standardSymplectic_top_right 2 0 2 (by decide)]; decide
  have h_03 : (standardSymplectic 2) 0 3 = 0 := by
    rw [standardSymplectic_top_right 2 0 3 (by decide)]; decide
  have h_10 : (standardSymplectic 2) 1 0 = 0 := by
    rw [standardSymplectic_top_right 2 1 0 (by decide)]; decide
  have h_11 : (standardSymplectic 2) 1 1 = 0 := by
    rw [standardSymplectic_top_right 2 1 1 (by decide)]; decide
  have h_12 : (standardSymplectic 2) 1 2 = 0 := by
    rw [standardSymplectic_top_right 2 1 2 (by decide)]; decide
  have h_13 : (standardSymplectic 2) 1 3 = 1 := by
    rw [standardSymplectic_top_right 2 1 3 (by decide)]; decide
  have h_20 : (standardSymplectic 2) 2 0 = -1 := by
    rw [standardSymplectic_bottom_left 2 2 0 (by decide)]; decide
  have h_21 : (standardSymplectic 2) 2 1 = 0 := by
    rw [standardSymplectic_bottom_left 2 2 1 (by decide)]; decide
  have h_22 : (standardSymplectic 2) 2 2 = 0 := by
    rw [standardSymplectic_bottom_left 2 2 2 (by decide)]; decide
  have h_23 : (standardSymplectic 2) 2 3 = 0 := by
    rw [standardSymplectic_bottom_left 2 2 3 (by decide)]; decide
  have h_30 : (standardSymplectic 2) 3 0 = 0 := by
    rw [standardSymplectic_bottom_left 2 3 0 (by decide)]; decide
  have h_31 : (standardSymplectic 2) 3 1 = -1 := by
    rw [standardSymplectic_bottom_left 2 3 1 (by decide)]; decide
  have h_32 : (standardSymplectic 2) 3 2 = 0 := by
    rw [standardSymplectic_bottom_left 2 3 2 (by decide)]; decide
  have h_33 : (standardSymplectic 2) 3 3 = 0 := by
    rw [standardSymplectic_bottom_left 2 3 3 (by decide)]; decide
  rw [h_00, h_01, h_02, h_03, h_10, h_11, h_12, h_13,
      h_20, h_21, h_22, h_23, h_30, h_31, h_32, h_33]
  push_cast
  ring

end JacobianChallenge

end
