/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodMatrix
import JacobianChallenge.Manifold.CompleteHodgeRiemannComplexTorus

set_option linter.unusedSectionVars false

/-! # Explicit period matrix entries on `T_L` (chip 20q)

For the complex torus `T_L = ℂ ⧸ L` with the explicit symplectic
basis from a lattice pair `(lam₁, lam₂)`, the period matrix
`periodMatrix data basis_g_dz cycleGens` is the `2 × 1` complex
matrix `[[lam₁], [lam₂]]`:

  `periodMatrix _ basis_g_dz cycleGens (Fin.cast … ⟨0,_⟩) ⟨0,_⟩ = lam₁`
  `periodMatrix _ basis_g_dz cycleGens (Fin.cast … ⟨1,_⟩) ⟨0,_⟩ = lam₂`

This is the in-tree extraction of the computation appearing inside
chip 19l (`completeHodgeRiemannHypothesis_complexTorus`), now exposed
as a standalone lemma for downstream consumers.

## What this file ships

* `periodMatrix_complexTorus_entry_zero` — `(0, 0)` entry equals `lam₁`.
* `periodMatrix_complexTorus_entry_one` — `(1, 0)` entry equals `lam₂`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`(0, 0)` entry of the period matrix on `T_L`**: integral of
`dz` over the basis loop at `lam₁` equals `lam₁`. -/
theorem periodMatrix_complexTorus_entry_zero
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) :
    periodMatrix (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens)
        ⟨0, by rw [genus_eq_one L]; decide⟩
        ⟨0, by rw [genus_eq_one L]; decide⟩
      = lam₁ := by
  -- Step 1: unfold periodMatrix → PeriodPairing data (cycleGens i) (α j).
  rw [periodMatrix_apply]
  -- Step 2: identify cycleGens at the reindexed Fin (2*1) index 0.
  rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
  -- Step 3: identify basis_g_dz at Fin g index 0 = dz L.
  have h_basis : basis_g_dz L (⟨0, by rw [genus_eq_one L]; decide⟩
      : Fin (JacobianChallenge.genus (ℂ ⧸ L))) = dz L := by
    rw [basis_g_dz_apply]
    rw [show finCongr (genus_eq_one L) ⟨0, by rw [genus_eq_one L]; decide⟩
          = (0 : Fin 1) from Subsingleton.elim _ _]
    exact basis_one_dz_apply L
  rw [h_basis]
  -- Step 4: apply the in-tree `complexPeriod_torusBasisLoop_dz` (period
  -- of dz over γ_{lam}-loop = lam).
  -- The cycleGens at index 0 unfolds to the lam₁-loop.
  -- Apply the in-tree period evaluation lemma.
  exact complexPeriod_torusBasisLoop_dz L lam₁ hlam₁

/-- **`(1, 0)` entry of the period matrix on `T_L`**: integral of
`dz` over the basis loop at `lam₂` equals `lam₂`. -/
theorem periodMatrix_complexTorus_entry_one
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L) :
    periodMatrix (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens)
        ⟨1, by rw [genus_eq_one L]; decide⟩
        ⟨0, by rw [genus_eq_one L]; decide⟩
      = lam₂ := by
  rw [periodMatrix_apply]
  rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
  have h_basis : basis_g_dz L (⟨0, by rw [genus_eq_one L]; decide⟩
      : Fin (JacobianChallenge.genus (ℂ ⧸ L))) = dz L := by
    rw [basis_g_dz_apply]
    rw [show finCongr (genus_eq_one L) ⟨0, by rw [genus_eq_one L]; decide⟩
          = (0 : Fin 1) from Subsingleton.elim _ _]
    exact basis_one_dz_apply L
  rw [h_basis]
  show PeriodPairing _ _ _ = _
  exact complexPeriod_torusBasisLoop_dz L lam₂ hlam₂

end ComplexTorus

end JacobianChallenge

end
