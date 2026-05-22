/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromSurfaceClassificationData
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityFromSesquilinearUpperTriangular
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationFromStrictUpperQ
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityNamed

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasJacobianHodgeChain X` from `g²` scalar identities + SCD

Composes the C3 wave's umbrella discharge with the existing HJHC
SCD-based constructor, giving HJHC from `g²` scalar identities + SCD.

The route:
* `g(g − 1)/2` strict-upper Q vanishing identities ⟹ `RiemannFirstBilinearRelation`
  (chip 20g named form).
* `g(g + 1)/2` upper-tri Petersson pairing identities ⟹ `RiemannSecondRelationPositivity`
  (this session's chip).
* RFBR + RSRP ⟹ `CompleteHodgeRiemannHypothesis` (chip 10).
* SCD + CHRH ⟹ `HasJacobianHodgeChain X` (in tree).

## What ships

* `HasJacobianHodgeChain.of_upperTriangularScalars` — constructor at
  general genus from `(SCD, basis_ω, g² scalar identities)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianHodgeChain X` from `g²` scalar identities + SCD,
at any genus.** -/
theorem HasJacobianHodgeChain.of_upperTriangularScalars
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_strict_Q :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        @riemannBilinearPeriodForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = 0)
    (h_upper_Qsq :
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) *
          @periodSesquilinearForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = (globalPettersonHermitianForm X).toFun (basis_ω i) (basis_ω j)) :
    HasJacobianHodgeChain X := by
  have h_first :
      @RiemannFirstBilinearRelation X _ _ _
        (PeriodPairingData.ofSmoothCycle X)
        scd.symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus X)) := by
    apply riemannFirstBilinearRelation_of_strictUpperTriangular_Q_zero
      (data := PeriodPairingData.ofSmoothCycle X) basis_ω
      scd.symplecticBasis.cycleGens
      (standardSymplectic_antisymm (JacobianChallenge.genus X))
    exact h_strict_Q
  have h_second :
      RiemannSecondRelationPositivity
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        scd.symplecticBasis.cycleGens :=
    riemannSecondRelationPositivity_of_pettersonForm_sesquilinearUpperTriangular
      basis_ω scd.symplecticBasis.cycleGens h_upper_Qsq
  have h_chrh :
      CompleteHodgeRiemannHypothesis
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        scd.symplecticBasis.cycleGens :=
    completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond
      (PeriodPairingData.ofSmoothCycle X) basis_ω
      scd.symplecticBasis.cycleGens h_first h_second
  exact HasJacobianHodgeChain.ofSurfaceClassificationData scd basis_ω h_chrh

end JacobianChallenge

end
