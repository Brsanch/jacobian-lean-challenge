/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChain
import JacobianChallenge.Manifold.CompleteHodgeRiemannComplexTorus
import JacobianChallenge.Manifold.ComplexTorusSmoothHurewiczFromBasis
import JacobianChallenge.Manifold.SmoothSymplecticBasisReindex

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain (ℂ ⧸ L)` from lattice ℤ-basis + orientation (chip 19m)

Composes the full chip 19 chain on T_L into a `HasJacobianHodgeChain
(ℂ ⧸ L)` witness. Specifically, the witness is provided by:

* `basis_ω := basis_g_dz L` (the dim-`genus (ℂ⧸L)` basis of
  `HolomorphicOneForm (ℂ⧸L)`),
* `basePoint := (0 : ℂ ⧸ L)`,
* `symplecticBasis := (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
  (genus_eq_one L)`,
* `hurewicz` — from `smoothHurewiczHypothesisTorus_holds_of_basis` +
  `SmoothHurewiczHypothesis.reindex`,
* `hHR` — from `completeHodgeRiemannHypothesis_complexTorus` (chip 19l).

The two named classical inputs are:

* `IsZBasisOfL L lam₁ lam₂` — `(lam₁, lam₂)` is a ℤ-basis of `L`;
* `0 < (star lam₁ * lam₂).im` — lattice-orientation condition.

## What this file ships

* `hasJacobianHodgeChain_complexTorus_of_basis_and_orientation` — the
  T_L instance constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`HasJacobianHodgeChain (ℂ ⧸ L)` from lattice ℤ-basis + orientation.**
The deep classical content of the Hodge–Riemann chain on T_L reduces to:
(a) the existence of a ℤ-basis of `L`, and (b) the lattice-orientation
condition `0 < Im(star lam₁ · lam₂)`. -/
theorem hasJacobianHodgeChain_complexTorus_of_basis_and_orientation
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h_basis : IsZBasisOfL L lam₁ lam₂)
    (h_orient : 0 < (star lam₁ * lam₂).im) :
    HasJacobianHodgeChain (ℂ ⧸ L) := by
  refine ⟨basis_g_dz L, (0 : ℂ ⧸ L),
    (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex (genus_eq_one L),
    ?_, ?_⟩
  · -- SmoothHurewiczHypothesis on the reindexed symplectic basis.
    exact SmoothHurewiczHypothesis.reindex
      (symplecticBasis L lam₁ lam₂ hlam₁ hlam₂)
      (genus_eq_one L)
      (smoothHurewiczHypothesisTorus_holds_of_basis lam₁ lam₂
        hlam₁ hlam₂ h_basis)
  · -- CompleteHodgeRiemannHypothesis (chip 19l).
    exact completeHodgeRiemannHypothesis_complexTorus L lam₁ lam₂
      hlam₁ hlam₂ h_orient

end ComplexTorus

end JacobianChallenge

end
