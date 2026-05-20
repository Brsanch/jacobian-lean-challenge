/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothHomologyDataPackage
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `SmoothHomologyDataPackage` on the complex torus `T_L = ℂ ⧸ L`,
unconditional

At genus 1 on `T_L`:

* `symplecticBasis` — the dim-`genus (ℂ⧸L)` symplectic basis
  `symplecticBasisG L` (reindex of the dim-1 `symplecticBasisOne L`
  along `genus_eq_one`).
* `hurewicz` — `smoothHurewiczHypothesisTorus_holds_of_basis` applied
  to `basisFin2OfL_isZBasisOfL` (universal-cover lifting + the
  homological decomposition + the ℤ-basis hypothesis), reindexed to
  dim `genus (ℂ ⧸ L)`.
* `bilinear` — `riemannBilinear_transport` applied to
  `basisFin2OfL_realLinearIndependent`.

All three named atoms are *unconditional* on `T_L`. This file
exhibits the resulting `SmoothHomologyDataPackage (basis_g_dz L)`
unconditionally, validating the single-input package structure at
genus 1.

## What this file ships

* `smoothHomologyDataPackage_complexTorus L` — unconditional inhabitant.
* `nonempty_smoothHomologyDataPackage_complexTorus L` — `Nonempty`
  packaging.
* `nonempty_periodLatticeSymplecticBundle_complexTorus_of_package` —
  end-to-end composition through `SmoothHomologyDataPackage` to
  `Nonempty (PeriodLatticeSymplecticBundle ... basis_g_dz)`. Reproduces
  the known unconditional T_L closure via the single-input route.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Unconditional `SmoothHomologyDataPackage (basis_g_dz L)` on `T_L`.**

Every field of the package is discharged from named unconditional
content already in tree:

* `basePoint := (0 : ℂ ⧸ L)` — canonical base point of the quotient.
* `symplecticBasis := symplecticBasisG L` — dim-`genus (ℂ⧸L)`
  reindex of the explicit dim-1 symplectic basis.
* `hurewicz` — `smoothHurewiczHypothesisTorus_holds_of_basis` +
  `basisFin2OfL_isZBasisOfL`, reindexed.
* `bilinear` — `riemannBilinear_transport` +
  `basisFin2OfL_realLinearIndependent`. -/
noncomputable def smoothHomologyDataPackage_complexTorus :
    SmoothHomologyDataPackage (X := ℂ ⧸ L) (basis_g_dz L) where
  basePoint := (0 : ℂ ⧸ L)
  symplecticBasis := symplecticBasisG L
  hurewicz := by
    -- SmoothHurewicz on the reindexed symplectic basis at dim `genus T_L`.
    -- Source: SmoothHurewiczHypothesisTorus on dim 1, reindexed.
    have hSH_torus :
        SmoothHurewiczHypothesisTorus L (lam₁_complexTorus L)
          (lam₂_complexTorus L) (lam₁_complexTorus_mem L)
          (lam₂_complexTorus_mem L) :=
      smoothHurewiczHypothesisTorus_holds_of_basis _ _ _ _
        basisFin2OfL_isZBasisOfL
    -- The torus Hurewicz is by definition the SmoothHurewiczHypothesis on
    -- the dim-1 symplecticBasis L _ _ _ _; reindex it to dim `genus T_L`.
    -- `symplecticBasisG L` is defined as `symplecticBasisOne L`.reindex `genus_eq_one`,
    -- and `symplecticBasisOne L = symplecticBasis L lam₁ lam₂ _ _`.
    exact
      SmoothHurewiczHypothesis.reindex (symplecticBasisOne L) (genus_eq_one L)
        hSH_torus
  bilinear :=
    riemannBilinear_transport L (lam₁_complexTorus L) (lam₂_complexTorus L)
      (lam₁_complexTorus_mem L) (lam₂_complexTorus_mem L)
      (basisFin2OfL_realLinearIndependent L)

/-- **`Nonempty` packaging of the unconditional `SmoothHomologyDataPackage`
on `T_L`.** -/
theorem nonempty_smoothHomologyDataPackage_complexTorus :
    Nonempty (SmoothHomologyDataPackage (X := ℂ ⧸ L) (basis_g_dz L)) :=
  ⟨smoothHomologyDataPackage_complexTorus L⟩

/-- **End-to-end validation: `Nonempty (PeriodLatticeSymplecticBundle ...)`
on `T_L` via the single-input package.**

Confirms the headline composite reproduces the known unconditional
T_L closure (cf. `nonempty_periodLatticeSymplecticBundle_complexTorus`). -/
theorem nonempty_periodLatticeSymplecticBundle_complexTorus_of_package :
    Nonempty
      (PeriodLatticeSymplecticBundle
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :=
  nonempty_periodLatticeSymplecticBundle_of_nonempty_smoothHomologyDataPackage
    (nonempty_smoothHomologyDataPackage_complexTorus L)

end ComplexTorus

end JacobianChallenge

end
