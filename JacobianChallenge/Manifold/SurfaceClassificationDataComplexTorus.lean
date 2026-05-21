/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SurfaceClassificationData
import JacobianChallenge.Manifold.SmoothHomologyDataPackageComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `SurfaceClassificationData` on the complex torus `T_L = ℂ ⧸ L`,
unconditional

At genus 1 on `T_L`, the three SCD atoms are *unconditional* in tree:

* `basePoint := (0 : ℂ ⧸ L)`.
* `symplecticBasis := symplecticBasisG L` (dim-`genus (ℂ⧸L)` reindex
  of the explicit dim-1 symplectic basis).
* `hurewicz` — `smoothHurewiczHypothesisTorus_holds_of_basis`
  applied to `basisFin2OfL_isZBasisOfL`, reindexed.

This file is the genus-1 counterpart to
`surfaceClassificationData_RiemannSphere`. It does **not** use the
`bilinear` discharge — that is the chip-19/20 content, which on T_L
also happens to be unconditional but is consumed separately at the
bridge `toSmoothHomologyDataPackage`.

## What this file ships

* `surfaceClassificationData_complexTorus L` — unconditional
  inhabitant.
* `nonempty_surfaceClassificationData_complexTorus L` — `Nonempty`
  packaging.
* `nonempty_smoothHomologyDataPackage_complexTorus_via_SCD` — smoke
  test that the SCD-bridge route reproduces the in-tree
  `Nonempty (SmoothHomologyDataPackage (basis_g_dz L))` on T_L when
  combined with the unconditional `bilinear` discharge.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module Submodule

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Unconditional `SurfaceClassificationData (ℂ ⧸ L)` on the complex
torus.** Bundles the three topological / homological atoms from the
existing in-tree T_L `SmoothHomologyDataPackage` construction.

* `basePoint := (0 : ℂ ⧸ L)` — canonical quotient zero.
* `symplecticBasis := symplecticBasisG L` — dim-`genus (ℂ⧸L)` reindex
  of `symplecticBasisOne L`.
* `hurewicz` — `smoothHurewiczHypothesisTorus_holds_of_basis` +
  `basisFin2OfL_isZBasisOfL`, reindexed via
  `SmoothHurewiczHypothesis.reindex`. -/
noncomputable def surfaceClassificationData_complexTorus :
    SurfaceClassificationData (ℂ ⧸ L) where
  basePoint := (0 : ℂ ⧸ L)
  symplecticBasis := symplecticBasisG L
  hurewicz := by
    have hSH_torus :
        SmoothHurewiczHypothesisTorus L (lam₁_complexTorus L)
          (lam₂_complexTorus L) (lam₁_complexTorus_mem L)
          (lam₂_complexTorus_mem L) :=
      smoothHurewiczHypothesisTorus_holds_of_basis _ _ _ _
        basisFin2OfL_isZBasisOfL
    exact
      SmoothHurewiczHypothesis.reindex (symplecticBasisOne L) (genus_eq_one L)
        hSH_torus

/-- **`Nonempty (SurfaceClassificationData (ℂ ⧸ L))` on T_L.** -/
theorem nonempty_surfaceClassificationData_complexTorus :
    Nonempty (SurfaceClassificationData (ℂ ⧸ L)) :=
  ⟨surfaceClassificationData_complexTorus L⟩

/-- **Smoke test: the SCD route reproduces the in-tree
`SmoothHomologyDataPackage (basis_g_dz L)` on T_L.**

Combines `surfaceClassificationData_complexTorus L` (chip 2) with the
unconditional `bilinear` discharge `riemannBilinear_transport ... +
basisFin2OfL_realLinearIndependent L` through the chip-1 bridge
`toSmoothHomologyDataPackage`, yielding
`Nonempty (SmoothHomologyDataPackage (basis_g_dz L))`. Matches
`nonempty_smoothHomologyDataPackage_complexTorus`. -/
theorem nonempty_smoothHomologyDataPackage_complexTorus_via_SCD :
    Nonempty (SmoothHomologyDataPackage (X := ℂ ⧸ L) (basis_g_dz L)) :=
  ⟨(surfaceClassificationData_complexTorus L).toSmoothHomologyDataPackage
    (riemannBilinear_transport L (lam₁_complexTorus L) (lam₂_complexTorus L)
      (lam₁_complexTorus_mem L) (lam₂_complexTorus_mem L)
      (basisFin2OfL_realLinearIndependent L))⟩

end ComplexTorus

end JacobianChallenge

end
