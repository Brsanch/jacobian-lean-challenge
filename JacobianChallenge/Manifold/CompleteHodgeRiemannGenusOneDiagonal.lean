/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromStandardSymplectic
import JacobianChallenge.Manifold.RiemannBilinearMatrixPosGenusOne

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` at genus 1 from diagonal positivity (chip 19h)

Composes chip 19f (1-input genus-1 reduction with
`J := standardSymplectic`) with chip 19g (matrix positivity from
diagonal positivity at genus 1) into a single discharge of
`CompleteHodgeRiemannHypothesis` from **one named input**:

  `∀ i, 0 < (i • Πᵀ J Π̄)_{ii}.re ∧ (i • Πᵀ J Π̄)_{ii}.im = 0`

which is the **diagonal positivity** of the period-matrix bilinear
form. At `genus X = 1`, `Fin (genus X)` is a singleton, so this is
effectively a single scalar inequality.

This is the deepest single-input form at genus 1; the remaining
classical content is just the diagonal-positivity check.

## What this file ships

* `completeHodgeRiemannHypothesis_of_diagonal_pos_genus_one` — the
  composed reduction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`CompleteHodgeRiemannHypothesis` at genus 1 from diagonal
positivity.** Composes the genus-1 first-relation discharge (chip 13)
with the diagonal-positivity-implies-matrix-positivity reduction
(chip 19g) and the chip 19f route. -/
theorem completeHodgeRiemannHypothesis_of_diagonal_pos_genus_one
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h_g : JacobianChallenge.genus X = 1)
    (h_diag_im : ∀ i : Fin (JacobianChallenge.genus X),
        (((Complex.I : ℂ) •
            periodMatrixForm (periodMatrix data basis_ω cycleGens)
              (standardSymplectic (JacobianChallenge.genus X))) i i).im = 0)
    (h_diag_re : ∀ i : Fin (JacobianChallenge.genus X),
        0 < (((Complex.I : ℂ) •
            periodMatrixForm (periodMatrix data basis_ω cycleGens)
              (standardSymplectic (JacobianChallenge.genus X))) i i).re) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  apply completeHodgeRiemannHypothesis_of_matrixPos_genus_one_standardSymp h_g
  exact riemannBilinearMatrixPos_of_diagonal_pos_genus_one h_g _ h_diag_im h_diag_re

end JacobianChallenge

end
