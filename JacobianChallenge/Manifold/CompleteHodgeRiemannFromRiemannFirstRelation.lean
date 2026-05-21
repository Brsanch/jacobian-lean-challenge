/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationNamed
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromUpperTriangularStandard

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` from `RiemannFirstBilinearRelation` + matrix-PD

The end-to-end composite at general genus: combines

* chip 9 (`RiemannFirstBilinearRelation`) — the substantive
  classical content of the first Riemann bilinear relation;
* chip 20p
  (`completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos`)
  — the in-tree reduction of CHRH to strict-upper-triangular + matrix
  positivity.

Composing the two: `CompleteHodgeRiemannHypothesis` follows from
`RiemannFirstBilinearRelation cycleGens (standardSymplectic g)` plus
the matrix-PD positivity input. The two named atoms are the
**minimal** classical content for general-genus CHRH after the chip 19/20
arc's structural reductions.

This composition explicitly verifies the per-genus open-content
summary in `OPEN.md` (2026-05-21 update):

  | `g` | first-relation atoms                                | PD content |
  | --- | -------------------------------------------------- | ---------- |
  | 0   | 0 (vacuous, chip 20a)                              | 0 (vacuous, chip 20a) |
  | 1   | 0 (auto from anti-sym, chip 13)                    | 1 scalar (chip 19h)   |
  | 2   | 1 entry `N 0 1 = 0` (chip 20h)                     | 2×2 Hermitian PD (chip 20r) |
  | g   | `g(g-1)/2` strict-upper entries (chip 20g/p)       | `g × g` Hermitian PD (chip 20p) |

The first-relation column is **uniformly** discharged by
`RiemannFirstBilinearRelation`; the PD column is the orthogonal
classical content.

## What this file ships

* `completeHodgeRiemannHypothesis_of_RiemannFirstBilinearRelation_matrixPos`
  — end-to-end constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **End-to-end CHRH from the two minimal named atoms.**

Takes:
* `data : PeriodPairingData X` — period pairing structure.
* `basis_ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` — chosen
  basis.
* `cycleGens : Fin (2 g) → data.H1` — symplectic homology basis.
* `h_first : RiemannFirstBilinearRelation cycleGens (standardSymplectic g)`
  — Riemann first relation (chip 9 named hypothesis).
* `hPos : ∀ x : Fin (genus X) → ℂ, x ≠ 0 →
    (star x ⬝ᵥ ((I • periodMatrixForm pmat standardSymplectic) *ᵥ x)).im = 0
    ∧ 0 < (star x ⬝ᵥ ((I • periodMatrixForm pmat standardSymplectic) *ᵥ x)).re`
  — matrix-PD positivity (chip 20p input).

Returns `CompleteHodgeRiemannHypothesis data basis_ω cycleGens`.

Composes chip 9
(`strictUpperTriangular_zero_of_RiemannFirstBilinearRelation` with
`J := standardSymplectic g` + `standardSymplectic_antisymm`) with
chip 20p
(`completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos`). -/
theorem completeHodgeRiemannHypothesis_of_RiemannFirstBilinearRelation_matrixPos
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (h_first :
      RiemannFirstBilinearRelation cycleGens
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
  completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos
    data basis_ω cycleGens
    (strictUpperTriangular_zero_of_RiemannFirstBilinearRelation
      basis_ω cycleGens h_first)
    hPos

end JacobianChallenge

end
