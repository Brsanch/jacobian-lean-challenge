/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromAntiSymm
import JacobianChallenge.Manifold.RiemannBilinearFirstRelationUpperTriangular

set_option linter.unusedSectionVars false

/-! # CHRH from (anti-sym J + strict-upper-triangular zero + matrix PD) (chip 20n)

Composes:

* chip 19e (`completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos`):
  CHRH ⟸ (anti-sym `J` + first relation + matrix PD);
* chip 20g (`riemannBilinearFirstRelation_of_offDiagonal_zero_of_antisymm`
  in its strict-upper-triangular form):
  anti-sym `J` + strict-upper-triangular zero ⟹ first relation.

Net: CHRH ⟸ (anti-sym `J` + strict-upper-triangular zero on
`pmatᵀ · J · pmat` + matrix PD on `i • pmatᵀ · J · pmat.map star`).

At low genus this collapses dramatically:

* `g = 0`: no strict-upper entries → CHRH ⟸ (anti-sym `J` + matrix PD).
  Matrix PD is vacuous (Fin 0) → CHRH unconditional (recovers chip 20a).
* `g = 1`: no strict-upper entries → CHRH ⟸ (anti-sym `J` + matrix PD).
  Matrix PD at g = 1 = diagonal positivity scalar (chip 19g).
* `g = 2`: 1 strict-upper entry + matrix PD on a 2×2 matrix.
* `g ≥ 3`: `g(g − 1)/2` strict-upper-triangular scalar equations +
  matrix PD on a `g × g` Hermitian matrix.

The remaining open content is exactly the classical "ω_i ∧ ω_j
integration" (first relation off-diagonal entries) + "Hodge inner
product positivity" (matrix PD) at general genus.

## What this file ships

* `completeHodgeRiemannHypothesis_of_antiSymm_upperTriangular_matrixPos` —
  the composite headline.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **CHRH from (anti-sym `J` + strict-upper-triangular zero + matrix PD).**

The "first relation" atom of `completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos`
(chip 19e) is discharged from the strict-upper-triangular zero
condition + the (free) anti-symmetry of `J` via chip 20g. -/
theorem completeHodgeRiemannHypothesis_of_antiSymm_upperTriangular_matrixPos
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    {J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ}
    (hJ : Jᵀ = -J)
    (h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        ((periodMatrix data basis_ω cycleGens)ᵀ * J.map ((↑) : ℤ → ℂ)
          * periodMatrix data basis_ω cycleGens) i j = 0)
    (hPos : ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
              *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens) J)
              *ᵥ x)).re) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  have hFirst :=
    (riemannBilinearFirstRelation_iff_strictUpperTriangular_zero_of_antisymm
      data basis_ω cycleGens hJ).mpr h_upper
  exact completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos
    hJ hFirst hPos

end JacobianChallenge

end
