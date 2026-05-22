/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentGenusTwoLiteral

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasJacobianAnalyticStructure X` at genus 2 from 4 explicit scalar identities

End-to-end constructor: at `genus X = 2`, the universal class
`HasJacobianAnalyticStructure X` follows from:

* `SurfaceClassificationData X`;
* a basis `basis_ω : Basis (Fin 2) ℂ (HolomorphicOneForm X)`;
* **4 explicit literal period-matrix scalar identities** at the upper
  triangle (1 bilinear strict-upper Q + 3 sesquilinear Petersson).

## What ships

* `HasJacobianAnalyticStructure.of_genus_two_literalScalars` —
  constructor at genus 2.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` at `genus X = 2` from 4 explicit
literal scalar identities + SCD.** -/
theorem HasJacobianAnalyticStructure.of_genus_two_literalScalars
    (h_g : JacobianChallenge.genus X = 2)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (i₀ i₁ : Fin (JacobianChallenge.genus X))
    (h_i₀ : i₀.val = 0) (h_i₁ : i₁.val = 1)
    (h_Q01 :
      @riemannBilinearPeriodForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₁) = 0)
    (h_pair_00 :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₀)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₀))
    (h_pair_01 :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₁)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₁))
    (h_pair_11 :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₁) (basis_ω i₁)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₁) (basis_ω i₁)) :
    HasJacobianAnalyticStructure X :=
  letI : HasJacobianClassicalContent X :=
    HasJacobianClassicalContent.of_genus_two h_g scd basis_ω i₀ i₁ h_i₀ h_i₁
      h_Q01 h_pair_00 h_pair_01 h_pair_11
  inferInstance

end JacobianChallenge

end
