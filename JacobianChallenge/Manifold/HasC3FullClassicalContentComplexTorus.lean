/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContent
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityComplexTorus
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationGenusOne
import JacobianChallenge.Manifold.ComplexTorusSmoothHurewiczFromBasis
import JacobianChallenge.Manifold.ComplexTorusOrientedBasis
import JacobianChallenge.Manifold.SmoothSymplecticBasisReindex
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # `HasC3FullClassicalContent` UNCONDITIONAL on `T_L = ℂ ⧸ L`

Composes the three substantive per-genus discharges at genus 1 on the
complex torus:

* **SCD on T_L** — explicit data from a positively-oriented ℤ-basis
  `(lam₁, lam₂)` of `L`:
  - `basePoint := (0 : ℂ ⧸ L)`;
  - `symplecticBasis := (symplecticBasis L lam₁ lam₂ _ _).reindex (genus_eq_one L)`;
  - `hurewicz` via `smoothHurewiczHypothesisTorus_holds_of_basis` (chip
    19l-style unconditional T_L Hurewicz) reindexed.
* **RFBR** — chip 25's `riemannFirstBilinearRelation_of_genus_one_standardSymplectic`
  at `genus (ℂ⧸L) = 1` + `FiniteDimensional ℂ (HolomorphicOneForm
  (ℂ⧸L))` (unconditional via `DiskChartCover.holomorphicOneFormFiniteDim_holds`).
* **RSRP** — chip 24's per-basis
  `riemannSecondRelationPositivity_complexTorus_of_oriented_basis` at
  the same `(lam₁, lam₂)`, fed by `h_orient : 0 < Im(star lam₁ · lam₂)`.

The positively-oriented witness is supplied by chip 19s
(`exists_positively_oriented_ZBasisOfL`), which case-splits on
orientation of the canonical `(lam₁_complexTorus, lam₂_complexTorus)`
pair and swaps if necessary.

This closes the **C3 umbrella class** unconditionally on `T_L`,
matching the existing RS unconditional instance. Composed with the
in-tree bridge `instHasJacobianAnalyticStructure_of_HasC3FullClassicalContent`,
it dispatches `HasJacobianAnalyticStructure (ℂ ⧸ L)` automatically.

## What this file ships

* `instHasC3FullClassicalContent_complexTorus L` — unconditional T_L
  instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Unconditional `HasC3FullClassicalContent (ℂ ⧸ L)`.**

Pulls a positively-oriented ℤ-basis `(lam₁, lam₂)` of `L` via
`exists_positively_oriented_ZBasisOfL`, builds the SCD on T_L at that
basis (reindexing the genus-1 symplectic basis to `genus (ℂ⧸L)`), then
composes chip 25 (RFBR g=1 polymorphic in cycleGens) with chip 24's
per-basis RSRP to discharge the umbrella class. -/
instance instHasC3FullClassicalContent_complexTorus :
    HasC3FullClassicalContent (ℂ ⧸ L) := by
  obtain ⟨lam₁, lam₂, hlam₁, hlam₂, h_basis, h_orient⟩ :=
    exists_positively_oriented_ZBasisOfL L
  haveI : FiniteDimensional ℂ (HolomorphicOneForm (ℂ ⧸ L)) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := ℂ ⧸ L))
  -- Build the SCD on T_L at this positively-oriented basis.
  let sbOne : SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L) 1 :=
    symplecticBasis L lam₁ lam₂ hlam₁ hlam₂
  let sbG : SmoothSymplecticBasis 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)
      (JacobianChallenge.genus (ℂ ⧸ L)) :=
    sbOne.reindex (genus_eq_one L)
  have hSH_torus :
      SmoothHurewiczHypothesisTorus L lam₁ lam₂ hlam₁ hlam₂ :=
    smoothHurewiczHypothesisTorus_holds_of_basis lam₁ lam₂ hlam₁ hlam₂
      h_basis
  let scd : SurfaceClassificationData (ℂ ⧸ L) :=
    { basePoint := (0 : ℂ ⧸ L)
      symplecticBasis := sbG
      hurewicz :=
        SmoothHurewiczHypothesis.reindex sbOne (genus_eq_one L)
          hSH_torus }
  -- Provide the umbrella's existential witness.
  refine ⟨scd, basis_g_dz L, ?_, ?_⟩
  · -- RFBR via chip 25 (g=1 + FD).
    exact @riemannFirstBilinearRelation_of_genus_one_standardSymplectic
      (ℂ ⧸ L) _ _ _ _ _ _ (genus_eq_one L) _
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
      scd.symplecticBasis.cycleGens
  · -- RSRP via chip 24's per-basis form on the same (lam₁, lam₂).
    exact riemannSecondRelationPositivity_complexTorus_of_oriented_basis
      L lam₁ lam₂ hlam₁ hlam₂ h_orient

end ComplexTorus

end JacobianChallenge

end
