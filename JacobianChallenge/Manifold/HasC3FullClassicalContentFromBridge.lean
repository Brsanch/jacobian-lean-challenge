/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContent
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityFromBridge

set_option linter.unusedSectionVars false

/-! # `HasC3FullClassicalContent X` from the Hodge–Riemann bridge

A constructor for the C3 wave umbrella class
`HasC3FullClassicalContent X` taking the bridge identity at `J :=
standardSymplectic g` for the canonical global Petersson Hermitian form
in place of the named atom `RiemannSecondRelationPositivity`.

The Petersson form `globalPettersonHermitianForm X` is
positive-definite unconditionally on every compact connected complex
1-manifold (`globalPettersonHermitianForm_isPositiveDefinite`, this
session), so the only remaining open input for the RSRP-side at any
genus is the bridge identity itself.

## What this file ships

* `HasC3FullClassicalContent.of_bridge_pettersonForm` — constructor
  taking `(SCD, basis_ω, RBFR, bridge for Petersson form)` →
  `HasC3FullClassicalContent X`.

## Significance

Provides an **alternative path** to the universal C3 umbrella class
that uses the analytically-honest Petersson form rather than a
matrix-derived H_can. Combined with this session's
`hodgeInnerProductHypothesis_holds`, the open inputs for the
universal `HasJacobianAnalyticStructure X` instance via this route
are:

* `SurfaceClassificationData X` (surface classification + smooth
  Hurewicz);
* `RiemannFirstBilinearRelation` (Stokes ∮ ω = 0 on null-homologous
  cycles, plus chip 20g's strict-upper-triangular reduction);
* `HodgeRiemannBridgeHypothesis` for the **canonical** Petersson
  Hermitian form (the analytic Stokes identity bridging period matrix
  to L² norm).

These are three named classical inputs, all with explicit witnesses
(no `Classical.choose` on the H side, unlike the H_can route).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X` from the Hodge–Riemann bridge
for the Petersson form.**

Constructor variant of `instHasC3FullClassicalContent_RiemannSphere`,
taking the bridge identity at `J = standardSymplectic g` for the
canonical Petersson Hermitian form. The H side of RSRP is then
discharged via `riemannSecondRelationPositivity_of_bridge_pettersonForm`. -/
theorem HasC3FullClassicalContent.of_bridge_pettersonForm
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_first :
      @RiemannFirstBilinearRelation X _ _ _
        (PeriodPairingData.ofSmoothCycle X)
        scd.symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (h_bridge :
      HodgeRiemannBridgeHypothesis
        (PeriodPairingData.ofSmoothCycle X)
        basis_ω
        scd.symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (globalPettersonHermitianForm X)) :
    HasC3FullClassicalContent X where
  out :=
    ⟨scd, basis_ω, h_first,
      riemannSecondRelationPositivity_of_bridge_pettersonForm
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        scd.symplecticBasis.cycleGens h_bridge⟩

end JacobianChallenge

end
