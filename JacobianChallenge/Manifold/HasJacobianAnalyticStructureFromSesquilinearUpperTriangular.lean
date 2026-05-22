/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromSesquilinearUpperTriangular

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from upper-triangular pairing identities

End-to-end constructor at general genus on any compact connected
complex 1-manifold:

  (SCD, basis_ω, RBFR, g(g+1)/2 upper-triangular Petersson-pairing
   identities) ⟹ HasJacobianAnalyticStructure X.

Composes `HasC3FullClassicalContent.of_sesquilinearUpperTriangular_pettersonForm`
with the in-tree global bridge
`instHasJacobianAnalyticStructure_of_HasC3FullClassicalContent`.

This is the **cleanest open-input expression** of
`HasJacobianAnalyticStructure X` at general genus on every compact
connected complex 1-manifold via the Petersson-form route:

* `SurfaceClassificationData X` (topology atom);
* `RiemannFirstBilinearRelation` (Stokes / first Riemann relation
  atom);
* `g(g + 1)/2` scalar pairing identities (Stokes / wedge / cup-product
  for the Petersson form — the deep open analytic content).

## What ships

* `HasJacobianAnalyticStructure.of_sesquilinearUpperTriangular_pettersonForm`
  — constructor at general genus.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` from upper-triangular
Petersson-pairing identities, at any genus.** End-to-end constructor. -/
theorem HasJacobianAnalyticStructure.of_sesquilinearUpperTriangular_pettersonForm
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_first :
      @RiemannFirstBilinearRelation X _ _ _
        (PeriodPairingData.ofSmoothCycle X)
        scd.symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) *
          @periodSesquilinearForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = (globalPettersonHermitianForm X).toFun (basis_ω i) (basis_ω j)) :
    HasJacobianAnalyticStructure X :=
  letI : HasC3FullClassicalContent X :=
    HasC3FullClassicalContent.of_sesquilinearUpperTriangular_pettersonForm
      scd basis_ω h_first h_upper
  inferInstance

end JacobianChallenge

end
