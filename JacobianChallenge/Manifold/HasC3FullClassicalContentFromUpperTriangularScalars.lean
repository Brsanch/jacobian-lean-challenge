/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromSesquilinearUpperTriangular
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationFromStrictUpperQ
import JacobianChallenge.Manifold.StandardSymplecticForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasC3FullClassicalContent X` from `g²` scalar identities + SCD

The cleanest decomposition of the C3 wave's universal classical
content at general genus. The two named atoms of the umbrella
(RBFR + RSRP) reduce as follows:

* **RBFR** (chip 9 named) ⟸ `g(g − 1)/2` scalar identities — the
  **strict-upper-triangular vanishing** of the bilinear period form on
  the basis pairs (chip 20g / `riemannFirstBilinearRelation_of_strictUpperTriangular_Q_zero`).

* **RSRP** (chip 18 named, Petersson-form route) ⟸ `g(g + 1)/2`
  scalar pairing identities — the **upper-triangular sesquilinear
  Petersson identities** (this session's
  `hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular`).

Total: `g(g − 1)/2 + g(g + 1)/2 = g²` scalar identities, plus the SCD
atom (topology + smooth Hurewicz).

## What ships

* `HasC3FullClassicalContent.of_upperTriangularScalars` — constructor
  at general genus from `(SCD, basis_ω, g(g − 1)/2 strict-upper Q
  vanishing, g(g + 1)/2 upper Petersson identities)`.

## Significance

The cleanest open-input expression of the C3 umbrella at general genus:
* SCD (topology atom);
* `g²` scalar identities on the basis (analytic atoms).

The Petersson-form positive-definiteness is unconditional (this
session). The two scalar families are the deep classical open content:
Stokes on null-homologous cycles (RBFR side) + Stokes/wedge/cup-product
for the Petersson form (RSRP side).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X` from `g²` scalar identities + SCD.** -/
theorem HasC3FullClassicalContent.of_upperTriangularScalars
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
    HasC3FullClassicalContent X := by
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
  exact HasC3FullClassicalContent.of_sesquilinearUpperTriangular_pettersonForm
    scd basis_ω h_first h_upper_Qsq

end JacobianChallenge

end
