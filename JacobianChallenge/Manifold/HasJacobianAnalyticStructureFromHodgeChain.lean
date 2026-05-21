/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.SmoothHomologyDataPackageFromHodgeChain

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from the Hodge–Riemann chain (chip 5)

This file ships a direct constructor for `HasJacobianAnalyticStructure
X` from the three named classical hypotheses:

* `SmoothSymplecticBasis` — 2g based loops at `basePoint`;
* `SmoothHurewiczHypothesis` — smooth-Hurewicz on the basis loops;
* `CompleteHodgeRiemannHypothesis` — `(J, H, PD, first, bridge)`.

These three together yield a `SmoothHomologyDataPackage basis_ω` (chip
4), which yields `HasJacobianAnalyticStructure X` via the existing
`of_hasSmoothHomologyDataPackage` bridge.

The chip-5 constructor packages these steps so downstream consumers
need only present the three classical hypotheses to get the
basis-anonymous analytic Jacobian structure.

## What this file ships

* `HasJacobianAnalyticStructure.of_hodgeChain` — direct constructor
  taking `(basis_ω, basePoint, symplecticBasis, hurewicz,
  CompleteHodgeRiemannHypothesis)` → `HasJacobianAnalyticStructure X`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` from the three named classical
hypotheses.** Composes chip 4 (SmoothHomologyDataPackage from Hodge
chain) with the existing `of_hasSmoothHomologyDataPackage` bridge. -/
theorem HasJacobianAnalyticStructure.of_hodgeChain
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (basePoint : X)
    (symplecticBasis :
      SmoothSymplecticBasis 𝓘(ℝ, ℂ) X basePoint (JacobianChallenge.genus X))
    (hurewicz : SmoothHurewiczHypothesis symplecticBasis)
    (hHR : CompleteHodgeRiemannHypothesis
      (PeriodPairingData.ofSmoothCycle X) basis_ω symplecticBasis.cycleGens) :
    HasJacobianAnalyticStructure X :=
  ⟨⟨basis_ω,
    nonempty_smoothHomologyDataPackage_of_hodgeChain basePoint
      symplecticBasis hurewicz hHR⟩⟩

end JacobianChallenge

end
