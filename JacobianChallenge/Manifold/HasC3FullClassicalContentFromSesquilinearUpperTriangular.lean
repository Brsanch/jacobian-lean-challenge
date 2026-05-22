/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromBridge
import JacobianChallenge.Manifold.HodgeRiemannBridgeSesquilinearUpperTriangular

set_option linter.unusedSectionVars false

/-! # `HasC3FullClassicalContent X` from upper-triangular Petersson-pairing identities

End-to-end constructor at general genus on any compact connected
complex 1-manifold:

  (SCD, basis_ω, RBFR, g(g+1)/2 upper-triangular pairing identities
   for Petersson form) ⟹ HasC3FullClassicalContent X.

Composes `hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular`
with `HasC3FullClassicalContent.of_bridge_pettersonForm`.

## What ships

* `HasC3FullClassicalContent.of_sesquilinearUpperTriangular_pettersonForm`
  — constructor at general genus from `g(g+1)/2` upper-triangular
  pairing identities.

## Significance

Documents the cleanest open-input layout for the universal C3 umbrella
at general genus on every compact connected complex 1-manifold:

* `SurfaceClassificationData X` — topology + smooth Hurewicz.
* `RiemannFirstBilinearRelation cycleGens (standardSymplectic g)` —
  Stokes ∮ ω = 0 on null-homologous cycles, reducing to
  strict-upper-triangular bilinear vanishing.
* `g(g+1)/2` scalar pairing identities — the deep classical Stokes /
  wedge / cup-product content (analytic side).

Petersson-side positivity is unconditional (this session); only the
above three categories of named hypotheses remain open at general
genus.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X` from upper-triangular
Petersson-pairing identities.**

Constructs the C3 umbrella class from
* a SurfaceClassificationData witness;
* a basis `basis_ω`;
* the first Riemann bilinear relation;
* the upper-triangular family of Petersson-form pairing identities. -/
theorem HasC3FullClassicalContent.of_sesquilinearUpperTriangular_pettersonForm
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
    HasC3FullClassicalContent X := by
  have h_bridge :=
    hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular
      (PeriodPairingData.ofSmoothCycle X) basis_ω
      scd.symplecticBasis.cycleGens
      (globalPettersonHermitianForm X) h_upper
  exact HasC3FullClassicalContent.of_bridge_pettersonForm scd basis_ω
    h_first h_bridge

end JacobianChallenge

end
