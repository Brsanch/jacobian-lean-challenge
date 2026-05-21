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

* an SCD witness `scd : SurfaceClassificationData X` — topological
  surface classification + smooth-Hurewicz;
* a chosen ℂ-basis `basis_ω` of `HolomorphicOneForm X`;
* `RiemannFirstBilinearRelation scd.cycleGens (standardSymplectic g)`
  — the first Riemann bilinear period relation (chip 9 named atom);
* `RiemannSecondRelationPositivity data basis_ω scd.cycleGens` —
  Hodge positivity on the period matrix (chip 18 named atom).

The SCD is bundled *existentially* rather than via a separate
`[HasSurfaceClassificationData X]` instance because the per-X
discharges of the Riemann relations pick a *specific* SCD: at genus 1
on `T_L`, chip 24 only fires on the positively-oriented symplectic
basis (one of `(lam₁, lam₂)` vs `(lam₂, lam₁)` depending on
orientation). Bundling the SCD in the existential lets each X-specific
instance choose the SCD that matches its Riemann discharge.

Once an instance fires (unconditional on `RS` via chips 3/11/19, and
on `T_L = ℂ ⧸ L` via chips 2/24/25 — see
`HasC3FullClassicalContentComplexTorus.lean`),
`HasJacobianAnalyticStructure X` follows via the bridge below.

## What this file ships

* `HasC3FullClassicalContent X` — class.
* `instHasSurfaceClassificationData_of_HasC3FullClassicalContent` —
  HSCD derived from the umbrella.
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
the three named classical Props of the C3 wave (SCD, RFBR, RSRP)
plus a chosen ℂ-basis `basis_ω` of `HolomorphicOneForm X`, all
sharing a single SCD witness.

The existential lets each X-specific instance pick the SCD that
matches the X-specific Riemann discharges (e.g., positively-oriented
symplectic basis on `T_L`). -/
class HasC3FullClassicalContent (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- A shared SCD witness + basis_ω + both Riemann atoms on the
  same cycleGens. -/
  out :
    ∃ (scd : SurfaceClassificationData X)
        (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
          (HolomorphicOneForm X)),
      @RiemannFirstBilinearRelation X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X)) ∧
      RiemannSecondRelationPositivity
          (PeriodPairingData.ofSmoothCycle X)
          basis_ω
          scd.symplecticBasis.cycleGens

/-- **HSCD is derivable from the umbrella.** -/
instance instHasSurfaceClassificationData_of_HasC3FullClassicalContent
    [h : HasC3FullClassicalContent X] :
    HasSurfaceClassificationData X where
  out := ⟨h.out.choose⟩

/-- **Bridge: `[HasC3FullClassicalContent X]` discharges
`HasJacobianAnalyticStructure X`.**

Extracts the bundled SCD + basis_ω + RFBR + RSRP via `Classical.choose`
on `out`, then composes through chip 18's CHRH-from-RFR-RSRP +
chip 4's HJHC-from-SCD + the global HJHC→HJAS bridge. -/
instance instHasJacobianAnalyticStructure_of_HasC3FullClassicalContent
    [h : HasC3FullClassicalContent X] :
    HasJacobianAnalyticStructure X := by
  obtain ⟨scd, basis_ω, h_first, h_second⟩ := h.out
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
chips 3 + 11 + 19. The SCD is the explicit genus-0 empty-basis
witness; RFBR and RSRP are polymorphic in cycleGens at g=0. -/
instance instHasC3FullClassicalContent_RiemannSphere :
    HasC3FullClassicalContent RiemannSphere where
  out :=
    ⟨surfaceClassificationData_RiemannSphere (Classical.arbitrary _),
     defaultHolomorphicOneFormBasis RiemannSphere,
     riemannFirstBilinearRelation_RiemannSphere _ _,
     riemannSecondRelationPositivity_RiemannSphere _ _ _⟩

end RiemannSphere

end JacobianChallenge

end
