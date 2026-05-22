/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrixAntiHermitian
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Closed form for `(pmᵀ * standardSymplectic 2.cast * pm)_{i, j}` at literal `g = 2`

For `pm : Matrix (Fin 4) (Fin 2) ℂ`, the bilinear matrix (no star)

  `B := pmᵀ * (standardSymplectic 2).cast * pm : Matrix (Fin 2) (Fin 2) ℂ`

admits a uniform closed form for every entry:

  `B_{i, j} = (pm_{0, i} · pm_{2, j} − pm_{2, i} · pm_{0, j})
            + (pm_{1, i} · pm_{3, j} − pm_{3, i} · pm_{1, j})`.

Diagonal entries `B_{i, i}` vanish by commutativity of `ℂ`. The strict
upper-triangular entry `B_{0, 1}` is the substantive content; chip
9's `RiemannFirstBilinearRelation` at `J = standardSymplectic 2`
reduces to `B_{0, 1} = 0`.

## What ships

* `periodMatrixBilinear_standardSymplectic_two_apply` — closed form.
* `periodMatrixBilinear_standardSymplectic_two_diagonal_zero` —
  diagonal is `0`.

No `sorry`, no `axiom`. -/

noncomputable section

open Matrix

namespace JacobianChallenge

/-- **Closed form for `(pmᵀ * (standardSymplectic 2).cast * pm)_{i, j}`.** -/
theorem periodMatrixBilinear_standardSymplectic_two_apply
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (i j : Fin 2) :
    ((pmᵀ * (standardSymplectic 2).map ((↑) : ℤ → ℂ)) * pm) i j
      = pm 0 i * pm 2 j + pm 1 i * pm 3 j
        - pm 2 i * pm 0 j - pm 3 i * pm 1 j := by
  -- Reduce to the periodMatrixForm shape by introducing a star-free analog.
  -- Direct expansion via Matrix.mul_apply and explicit Fin 4 sums.
  rw [show (((pmᵀ : Matrix (Fin 2) (Fin 4) ℂ)
        * (standardSymplectic 2).map ((↑) : ℤ → ℂ)) * pm) i j
      = ∑ k : Fin 4, ((pmᵀ : Matrix (Fin 2) (Fin 4) ℂ)
            * (standardSymplectic 2).map ((↑) : ℤ → ℂ)) i k * pm k j
      from Matrix.mul_apply ..]
  have h_inner : ∀ k : Fin 4,
      ((pmᵀ : Matrix (Fin 2) (Fin 4) ℂ)
        * (standardSymplectic 2).map ((↑) : ℤ → ℂ)) i k
        = ∑ l : Fin 4, pm l i * ((standardSymplectic 2) l k : ℂ) := by
    intro k
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    show (pmᵀ) i l * ((standardSymplectic 2).map ((↑) : ℤ → ℂ)) l k
        = pm l i * ((standardSymplectic 2) l k : ℂ)
    rw [Matrix.transpose_apply, Matrix.map_apply]
  simp_rw [h_inner, Finset.sum_mul, Fin.sum_univ_four]
  -- Substitute standardSymplectic 2 entries (16 values).
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

/-- **The bilinear form's diagonal is `0` at `g = 2`.** -/
theorem periodMatrixBilinear_standardSymplectic_two_diagonal_zero
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (i : Fin 2) :
    ((pmᵀ * (standardSymplectic 2).map ((↑) : ℤ → ℂ)) * pm) i i = 0 := by
  rw [periodMatrixBilinear_standardSymplectic_two_apply]
  ring

end JacobianChallenge

end
