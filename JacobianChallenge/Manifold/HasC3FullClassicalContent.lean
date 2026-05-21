/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromHSCDRiemann
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationGenusZero
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityGenusZero
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `HasC3FullClassicalContent X` — umbrella class for the C3 wave

Bundles the three named classical Props that gate the C3 wave's
universality blocker into a single Prop typeclass:

* `[HasSurfaceClassificationData X]` — topological surface
  classification + smooth-Hurewicz.
* RFBR on the canonical SCD's cycleGens and `standardSymplectic g`.
* RSRP on the canonical SCD's cycleGens, against a specified
  basis_ω.

Once instances of this umbrella class fire (unconditional on RS via
chips 3/11/19), `HasJacobianAnalyticStructure X` follows via the
chip 20 composite + global HJHC→HJAS bridge.

The umbrella class is the ergonomic entry point for downstream
consumers that need "all three named atoms hold for X": they declare
`[HasC3FullClassicalContent X]` and get HJAS through typeclass
synthesis.

## What this file ships

* `HasC3FullClassicalContent X` — class.
* `instHasJacobianAnalyticStructure_of_HasC3FullClassicalContent` —
  bridge to HJAS.
* `instHasC3FullClassicalContent_RiemannSphere` — unconditional RS
  instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X`** — umbrella Prop class bundling
the three named classical Props of the C3 wave.

Includes:
* `[HasSurfaceClassificationData X]` as a typeclass instance (its
  presence is required for the SCD-derived fields below to even type-
  check at the canonical extractor).
* `riemannFirst` — RFBR on the canonical SCD's cycleGens.
* A *chosen* `basis_ω` plus the RSRP positivity on it.

Note: the basis_ω is bundled in so the class is X-only (no extra
parameters). Downstream consumers extract it via `chosenBasis_ω`. -/
class HasC3FullClassicalContent (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- HSCD is required. -/
  hasSCD : HasSurfaceClassificationData X
  /-- RFBR holds on the canonical SCD's cycleGens against
  `standardSymplectic`. -/
  riemannFirst :
    let scd := @canonicalSurfaceClassificationData X _ _ _ _ _ _ hasSCD
    @RiemannFirstBilinearRelation X _ _ _
      (PeriodPairingData.ofSmoothCycle X)
      scd.symplecticBasis.cycleGens
      (standardSymplectic (JacobianChallenge.genus X))
  /-- The existence of some basis_ω for which RSRP holds on the
  canonical SCD's cycleGens. -/
  riemannSecondExists :
    let scd := @canonicalSurfaceClassificationData X _ _ _ _ _ _ hasSCD
    ∃ basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
        (HolomorphicOneForm X),
      RiemannSecondRelationPositivity
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        scd.symplecticBasis.cycleGens

attribute [instance] HasC3FullClassicalContent.hasSCD

/-- **Bridge: `[HasC3FullClassicalContent X]` discharges
`HasJacobianAnalyticStructure X`.**

Composes through chip 4 + chip 18 to fire `HasJacobianHodgeChain X`,
which the existing in-tree global instance lifts to HJAS. -/
instance instHasJacobianAnalyticStructure_of_HasC3FullClassicalContent
    [h : HasC3FullClassicalContent X] :
    HasJacobianAnalyticStructure X := by
  obtain ⟨basis_ω, h_second⟩ := h.riemannSecondExists
  let scd := canonicalSurfaceClassificationData X
  have h_first := h.riemannFirst
  haveI : HasJacobianHodgeChain X :=
    HasJacobianHodgeChain.ofSurfaceClassificationData scd basis_ω
      (completeHodgeRiemannHypothesis_of_RiemannFirst_RiemannSecond
        (PeriodPairingData.ofSmoothCycle X) basis_ω
        scd.symplecticBasis.cycleGens h_first h_second)
  exact inferInstance

/-! ## Instance: `RiemannSphere` -/

namespace RiemannSphere

set_option maxHeartbeats 800000 in
/-- **Unconditional `HasC3FullClassicalContent RiemannSphere`** via
chips 3 + 11 + 19. -/
instance instHasC3FullClassicalContent_RiemannSphere :
    HasC3FullClassicalContent RiemannSphere where
  hasSCD := instHasSurfaceClassificationData_RiemannSphere
  riemannFirst :=
    riemannFirstBilinearRelation_RiemannSphere _ _
  riemannSecondExists :=
    ⟨defaultHolomorphicOneFormBasis RiemannSphere,
      riemannSecondRelationPositivity_RiemannSphere _ _ _⟩

end RiemannSphere

end JacobianChallenge

end
