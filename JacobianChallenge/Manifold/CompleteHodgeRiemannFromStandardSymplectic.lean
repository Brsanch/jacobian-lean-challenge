/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromAntiSymm
import JacobianChallenge.Manifold.StandardSymplecticForm
import JacobianChallenge.Manifold.RiemannBilinearFirstRelationGenusOne

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` from `standardSymplectic g` + 2 named inputs (chip 19f)

Specializes chip 19e (`completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos`)
to `J := standardSymplectic g`. Drops the `hJ` premise (the standard
symplectic is unconditionally anti-symmetric via
`standardSymplectic_antisymm`). The remaining two named inputs are:

* the **first relation** `Πᵀ · standardSymplectic · Π = 0`;
* the **matrix positivity** of `i • periodMatrixForm pm (standardSymplectic g)`.

Plus a **genus-1 corollary**: at `genus X = 1` the first relation is
automatic (chip 13), so `CompleteHodgeRiemannHypothesis` reduces to
just the **matrix positivity** input.

## What this file ships

* `completeHodgeRiemannHypothesis_of_first_matrixPos_standardSymp` —
  2-input specialization.
* `completeHodgeRiemannHypothesis_of_matrixPos_genus_one_standardSymp` —
  1-input specialization at genus 1.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **2-input specialization with `J := standardSymplectic g`.**
Drops `hJ` (always anti-symmetric); leaves the first relation and
matrix positivity as separate inputs. -/
theorem completeHodgeRiemannHypothesis_of_first_matrixPos_standardSymp
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (hFirst : RiemannBilinearFirstRelation data basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (hPos : ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens)
                  (standardSymplectic (JacobianChallenge.genus X)))
              *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens)
                  (standardSymplectic (JacobianChallenge.genus X)))
              *ᵥ x)).re) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens :=
  completeHodgeRiemannHypothesis_of_antiSymm_first_matrixPos
    (standardSymplectic_antisymm (JacobianChallenge.genus X))
    hFirst hPos

/-- **1-input specialization at genus 1 with `J := standardSymplectic g`.**
At `genus X = 1` the first relation is automatic (chip 13's
`riemannBilinearFirstRelation_of_antisymmetric_genus_one`). Only the
matrix positivity remains as a named input. -/
theorem completeHodgeRiemannHypothesis_of_matrixPos_genus_one_standardSymp
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h_g : JacobianChallenge.genus X = 1)
    (hPos : ∀ x : Fin (JacobianChallenge.genus X) → ℂ, x ≠ 0 →
        (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens)
                  (standardSymplectic (JacobianChallenge.genus X)))
              *ᵥ x)).im = 0 ∧
          0 < (star x ⬝ᵥ
            (((Complex.I : ℂ) •
                periodMatrixForm (periodMatrix data basis_ω cycleGens)
                  (standardSymplectic (JacobianChallenge.genus X)))
              *ᵥ x)).re) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens :=
  completeHodgeRiemannHypothesis_of_first_matrixPos_standardSymp
    (riemannBilinearFirstRelation_of_antisymmetric_genus_one
      data basis_ω cycleGens
      (standardSymplectic_antisymm (JacobianChallenge.genus X))
      h_g)
    hPos

end JacobianChallenge

end
