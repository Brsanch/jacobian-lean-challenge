/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromRiemannFirstRelation

set_option linter.unusedSectionVars false

/-! # `RiemannSecondRelationPositivity` — named-hypothesis form

The second Riemann bilinear relation, as required by chip 20p
(`completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos`),
is the positive-definiteness condition on
`i · pmatᵀ · J · pmat^*` (the Hodge inner product matrix). This file
names that condition as `RiemannSecondRelationPositivity data
basis_ω cycleGens`, symmetric to chip 9's `RiemannFirstBilinearRelation`.

Composed with chip 10
(`completeHodgeRiemannHypothesis_of_RiemannFirstBilinearRelation_matrixPos`),
this gives CHRH from the two minimal named atoms:

* `RiemannFirstBilinearRelation cycleGens (standardSymplectic g)` (chip 9).
* `RiemannSecondRelationPositivity data basis_ω cycleGens` (this chip).

Both are substantive Riemann period content; the C3 wave's open
content for items 5/11/12/13/17/18/21 (modulo the SCD topological
atoms) reduces to these two named Props.

## What this file ships

* `RiemannSecondRelationPositivity data basis_ω cycleGens` — Prop.
* `completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond` —
  CHRH from both named atoms.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannSecondRelationPositivity`** — the named classical
hypothesis that the Hodge inner product matrix `i · pmatᵀ · J · pmat^*`
is positive-definite on `Fin (genus X) → ℂ`.

Symmetric to chip 9's `RiemannFirstBilinearRelation`; this is the
chip 20p `hPos` input named. -/
def RiemannSecondRelationPositivity
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) : Prop :=
  ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
    (star x ⬝ᵥ
        (((Complex.I : ℂ) •
            periodMatrixForm (periodMatrix data basis_ω cycleGens)
              (standardSymplectic (JacobianChallenge.genus X)))
          *ᵥ x)).im = 0 ∧
      0 < (star x ⬝ᵥ
        (((Complex.I : ℂ) •
            periodMatrixForm (periodMatrix data basis_ω cycleGens)
              (standardSymplectic (JacobianChallenge.genus X)))
          *ᵥ x)).re

/-- **End-to-end CHRH from the two minimal named atoms.**

Combines chip 9 (`RiemannFirstBilinearRelation`) with the chip 18
`RiemannSecondRelationPositivity` via chip 10. The C3 wave's open
content at general genus for the CHRH chain is precisely these two
named Props. -/
theorem completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (h_first :
      RiemannFirstBilinearRelation cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (h_second :
      RiemannSecondRelationPositivity data basis_ω cycleGens) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens :=
  completeHodgeRiemannHypothesis_of_RiemannFirstBilinearRelation_matrixPos
    data basis_ω cycleGens h_first h_second

end JacobianChallenge

end
