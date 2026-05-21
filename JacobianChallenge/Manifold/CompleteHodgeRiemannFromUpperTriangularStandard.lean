/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromUpperTriangular
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false

/-! # CHRH from (strict-upper triangular + matrix PD) with J := standardSymplectic (chip 20p)

Specializes chip 20n
(`completeHodgeRiemannHypothesis_of_antiSymm_upperTriangular_matrixPos`)
to `J := standardSymplectic g`, absorbing the `hJ : Jᵀ = -J`
parameter via `standardSymplectic_antisymm`.

User-facing inputs at general genus reduce to two atoms:

* `h_upper` — strict-upper-triangular zero condition on
  `pmatᵀ · standardSymplectic.cast · pmat`. At low genus, this
  collapses: `g = 0` and `g = 1` have no strict-upper entries
  (automatic); `g = 2` has 1; `g ≥ 3` has `g(g − 1)/2`.
* `hPos` — matrix positivity on
  `i • pmatᵀ · standardSymplectic.cast · pmat.map star`.

## What this file ships

* `completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos`
  — the specialization.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **CHRH from `J := standardSymplectic` + strict-upper-triangular
zero + matrix PD.** Specialization of chip 20n with the `hJ` parameter
absorbed via `standardSymplectic_antisymm`. -/
theorem completeHodgeRiemannHypothesis_of_standardSymplectic_upperTriangular_matrixPos
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1)
    (h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        ((periodMatrix data basis_ω cycleGens)ᵀ
            * (standardSymplectic
                (JacobianChallenge.genus X)).map ((↑) : ℤ → ℂ)
          * periodMatrix data basis_ω cycleGens) i j = 0)
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
  completeHodgeRiemannHypothesis_of_antiSymm_upperTriangular_matrixPos
    (standardSymplectic_antisymm _) h_upper hPos

end JacobianChallenge

end
