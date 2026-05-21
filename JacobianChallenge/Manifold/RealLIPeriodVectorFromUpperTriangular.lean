/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannFromUpperTriangular
import JacobianChallenge.Manifold.BilinearFromHodgeChain

set_option linter.unusedSectionVars false

/-! # ℝ-LI of period vectors from the minimal-inputs bundle (chip 20o)

Composes chip 20n
(`completeHodgeRiemannHypothesis_of_antiSymm_upperTriangular_matrixPos`)
with chip 3 (`realLI_periodVector_of_completeHodgeRiemann`) to give:

  `LinearIndependent ℝ (periodVector data α (cycleGens i))`
  ⟸ (anti-sym `J` + strict-upper-triangular zero +
  matrix positivity)

This is the **direct minimal-inputs discharge** of the `bilinear`
field of `SmoothHomologyDataPackage` at general genus from
purely classical content (no Hodge-form choice, no separate first-
relation atom).

## What this file ships

* `realLI_periodVector_of_antiSymm_upperTriangular_matrixPos` —
  the composite headline.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **ℝ-LI of period vectors from minimal classical inputs.** Discharge of
the `bilinear` field of `SmoothHomologyDataPackage` at general genus
from anti-sym `J` + strict-upper-triangular zero + matrix PD. -/
theorem realLI_periodVector_of_antiSymm_upperTriangular_matrixPos
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
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector data basis_ω (cycleGens i)) :=
  realLI_periodVector_of_completeHodgeRiemann
    (completeHodgeRiemannHypothesis_of_antiSymm_upperTriangular_matrixPos
      hJ h_upper hPos)

end JacobianChallenge

end
