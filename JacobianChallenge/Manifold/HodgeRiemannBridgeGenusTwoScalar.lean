/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeRiemannBridge
import JacobianChallenge.Manifold.HodgeRiemannBridgeUpperTriangular
import JacobianChallenge.Manifold.PeriodMatrixFormStandardSymplecticDiagonalReal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Bridge identity at literal `g = 2` reduces to 3 scalar identities

At literal `Fin 4 / Fin 2` dimensions, the matrix bridge identity for
`J = standardSymplectic 2` reduces to **3 scalar identities** at the
upper-triangle entries `(0, 0)`, `(0, 1)`, `(1, 1)` via Hermitian
symmetry of both sides:

  * `(0, 0)`: `H(ω₀, ω₀) = 2 · (Im(star pm_{0,0} · pm_{2,0})
                                + Im(star pm_{1,0} · pm_{3,0}))`
    (real number, closed form from chip's `_diagonal_re` at g = 2).
  * `(1, 1)`: same with index 1.
  * `(0, 1)`: complex closed form (full off-diagonal expansion).

## What ships

* `hodgeRiemannBridgeHypothesis_at_genus_two_literal_of_three_scalars`
  — at `g = 2` literal, three scalar identities give the matrix
  bridge (with H matching the literal-Fin-4 / Fin-2 dimensions).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

/-- **At literal `g = 2`, the bridge identity ⟸ three scalar identities
on the upper triangle.**

This is the literal-Fin form: the user supplies the full `pm : Matrix
(Fin 4) (Fin 2) ℂ` and `H_mat : Matrix (Fin 2) (Fin 2) ℂ` (Hermitian),
together with the 3 upper-triangle scalar equations on `i • M = H_mat`.
Conclusion: the full 2 × 2 matrix bridge `i • periodMatrixForm pm
(standardSymplectic 2) = H_mat`. -/
theorem iPeriodMatrixForm_standardSymplectic_two_eq_of_three_scalars
    (pm : Matrix (Fin 4) (Fin 2) ℂ) (H_mat : Matrix (Fin 2) (Fin 2) ℂ)
    (h_H_herm : H_matᴴ = H_mat)
    (h_00 :
      ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) 0 0
        = H_mat 0 0)
    (h_01 :
      ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) 0 1
        = H_mat 0 1)
    (h_11 :
      ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) 1 1
        = H_mat 1 1) :
    ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) = H_mat := by
  -- LHS is Hermitian via chip 19a + standardSymplectic_antisymm.
  have h_LHS_herm :
      ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)).IsHermitian :=
    iPeriodMatrixForm_isHermitian pm (standardSymplectic 2)
      (standardSymplectic_antisymm 2)
  -- Matrix equality: pointwise check at all 4 entries.
  funext i j
  fin_cases i
  · fin_cases j
    · exact h_00
    · exact h_01
  · fin_cases j
    · -- (1, 0) entry: use Hermitian symmetry of both sides + h_01.
      show ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) 1 0
          = H_mat 1 0
      have h_LHS_swap :
          ((Complex.I : ℂ) • periodMatrixForm pm (standardSymplectic 2)) 1 0
            = star (((Complex.I : ℂ) • periodMatrixForm pm
                (standardSymplectic 2)) 0 1) := by
        have h := congrFun (congrFun h_LHS_herm 0) 1
        change star (((Complex.I : ℂ) • periodMatrixForm pm
                (standardSymplectic 2)) 1 0)
            = ((Complex.I : ℂ) • periodMatrixForm pm
                (standardSymplectic 2)) 0 1 at h
        rw [← h, star_star]
      have h_H_swap : H_mat 1 0 = star (H_mat 0 1) := by
        have h := congrFun (congrFun h_H_herm 0) 1
        change star (H_mat 1 0) = H_mat 0 1 at h
        rw [← h, star_star]
      rw [h_LHS_swap, h_01, ← h_H_swap]
    · exact h_11

end JacobianChallenge

end
