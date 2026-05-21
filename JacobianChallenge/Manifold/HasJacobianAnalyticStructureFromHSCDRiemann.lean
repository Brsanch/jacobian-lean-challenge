/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromSurfaceClassificationData
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityNamed

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from HSCD + RFBR + RSRP

The headline composite for the C3 universality blocker. Combines:

* **HSCD** — `[HasSurfaceClassificationData X]` (chips 1-3:
  topological surface classification + smooth-Hurewicz).
* **RFBR** — `RiemannFirstBilinearRelation cycleGens (standardSymplectic g)`
  (chip 9, factored via chip 16 into per-pair Riemann period
  identities).
* **RSRP** — `RiemannSecondRelationPositivity data basis_ω cycleGens`
  (chip 18, the matrix-PD positivity).

These three named Props are the **minimal classical content** for an
unconditional `HasJacobianAnalyticStructure X` instance at general
genus. The composite produces a `HasJacobianHodgeChain X` instance
(via chip 4 + chip 18's CHRH composite), which in turn fires
`HasJacobianAnalyticStructure X` via the in-tree global instance.

Once `HasJacobianAnalyticStructure X` fires unconditionally, items
5/11/12/13/17/18/21 flip via the C3 rewire of `JacobianChallenge.
Jacobian X` to `CanonicalAnalyticJacobianAnonymous X`.

## What this file ships

* `HasJacobianHodgeChain.of_HSCD_RFBR_RSRP` — typeclass form: HSCD +
  RFBR + RSRP discharges HJHC.
* `HasJacobianAnalyticStructure.of_HSCD_RFBR_RSRP` — typeclass form:
  HSCD + RFBR + RSRP discharges HJAS (via the global HJHC → HJAS
  instance).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianHodgeChain X` from the three named atoms.**

Combines:
* `[HasSurfaceClassificationData X]` (HSCD via canonical extractor).
* A chosen basis `basis_ω`.
* `RiemannFirstBilinearRelation` (RFBR) on the SCD's cycleGens.
* `RiemannSecondRelationPositivity` (RSRP) on the SCD's cycleGens. -/
theorem HasJacobianHodgeChain.of_HSCD_RFBR_RSRP
    [HasSurfaceClassificationData X]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_first :
      @RiemannFirstBilinearRelation X _ _ _ (PeriodPairingData.ofSmoothCycle X)
        (canonicalSurfaceClassificationData X).symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (h_second :
      RiemannSecondRelationPositivity
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        (canonicalSurfaceClassificationData X).symplecticBasis.cycleGens) :
    HasJacobianHodgeChain X :=
  let scd := canonicalSurfaceClassificationData X
  HasJacobianHodgeChain.ofSurfaceClassificationData scd basis_ω
    (completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond
      (PeriodPairingData.ofSmoothCycle X) basis_ω
      scd.symplecticBasis.cycleGens h_first h_second)

/-- **`HasJacobianAnalyticStructure X` from the three named atoms.**

Composes `HasJacobianHodgeChain.of_HSCD_RFBR_RSRP` with the global
instance `instHasJacobianAnalyticStructure_of_HasJacobianHodgeChain`.

This is the C3 wave's universal headline: the three minimal named
classical statements (HSCD + RFBR + RSRP) discharge the universality
blocker that gates Basic.lean items 5/11/12/13/17/18/21. -/
theorem HasJacobianAnalyticStructure.of_HSCD_RFBR_RSRP
    [HasSurfaceClassificationData X]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_first :
      @RiemannFirstBilinearRelation X _ _ _ (PeriodPairingData.ofSmoothCycle X)
        (canonicalSurfaceClassificationData X).symplecticBasis.cycleGens
        (standardSymplectic (JacobianChallenge.genus X)))
    (h_second :
      RiemannSecondRelationPositivity
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        (canonicalSurfaceClassificationData X).symplecticBasis.cycleGens) :
    HasJacobianAnalyticStructure X :=
  let _ : HasJacobianHodgeChain X :=
    HasJacobianHodgeChain.of_HSCD_RFBR_RSRP basis_ω h_first h_second
  inferInstance

end JacobianChallenge

end
