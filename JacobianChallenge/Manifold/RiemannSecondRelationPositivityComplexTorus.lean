/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityGenusOne
import JacobianChallenge.Manifold.ComplexTorusOrientedBasis
import JacobianChallenge.Manifold.CompleteHodgeRiemannComplexTorus
import JacobianChallenge.Manifold.SmoothSymplecticBasisReindex

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-! # `RiemannSecondRelationPositivity` UNCONDITIONAL on `T_L`

Composes chip 23
(`riemannSecondRelationPositivity_of_genus_one_of_lattice_orientation`)
with the in-tree T_L positively-oriented ℤ-basis chain (chip 19q +
chip 19s `exists_positively_oriented_ZBasisOfL`) to discharge RSRP
**unconditionally** on `T_L = ℂ ⧸ L` for some choice of basis and
symplectic basis.

This closes the substantive analytic content of the RSRP atom at g=1
on T_L — no named hypotheses remain.

## What this file ships

* `exists_riemannSecondRelationPositivity_complexTorus` — `Nonempty`-
  style headline: there exist `lam₁, lam₂ ∈ L` such that RSRP holds
  on the corresponding symplectic basis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`RiemannSecondRelationPositivity` UNCONDITIONAL on T_L.**

Pick a positively-oriented ℤ-basis `(lam₁, lam₂)` of `L` (chip 19s),
set up the symplectic basis from it, identify the periods
(`PeriodPairing data sb.cycleGens ⟨0,_⟩ (dz L) = lam₁` etc., via the
chip 19l identification chain), then apply chip 23 with `k₀ = ⟨0,_⟩,
k₁ = ⟨1,_⟩` and `h_orient = (0 < (star lam₁ * lam₂).im)`.

Returns the existence of `(lam₁, lam₂)` with the RSRP property holding
against the reindexed symplectic basis at `genus (ℂ ⧸ L) = 1`. -/
theorem exists_riemannSecondRelationPositivity_complexTorus :
    ∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),
      RiemannSecondRelationPositivity
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens) := by
  obtain ⟨lam₁, lam₂, hlam₁, hlam₂, _hZ, h_orient⟩ :=
    exists_positively_oriented_ZBasisOfL L
  refine ⟨lam₁, lam₂, hlam₁, hlam₂, ?_⟩
  -- Setup mirroring `completeHodgeRiemannHypothesis_complexTorus`.
  have hg : JacobianChallenge.genus (ℂ ⧸ L) = 1 := genus_eq_one L
  have h2g : 0 < 2 * JacobianChallenge.genus (ℂ ⧸ L) := by rw [hg]; decide
  have h2g' : 1 < 2 * JacobianChallenge.genus (ℂ ⧸ L) := by rw [hg]; decide
  have hg' : 0 < JacobianChallenge.genus (ℂ ⧸ L) := by rw [hg]; decide
  set k₀ : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) := ⟨0, h2g⟩
  set k₁ : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) := ⟨1, h2g'⟩
  set i₀ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) := ⟨0, hg'⟩
  set sb := symplecticBasis L lam₁ lam₂ hlam₁ hlam₂
  -- Apply chip 23 with k₀, k₁, i₀.
  apply riemannSecondRelationPositivity_of_genus_one_of_lattice_orientation
    hg _ _ _ k₀ k₁ rfl rfl i₀
  -- Goal: 0 < Im(star (pmat k₀ i₀) · pmat k₁ i₀)
  -- Identify pmat = periodMatrix at the T_L symplectic basis.
  -- pmat k₀ i₀ = periodMatrix data (basis_g_dz L) ((sb.reindex hg).cycleGens) k₀ i₀
  --            = PeriodPairing ... ((sb.reindex hg).cycleGens k₀) (basis_g_dz L i₀)
  --            = PeriodPairing ... (sb.cycleGens (Fin.cast _ k₀)) (basis_g_dz L i₀).
  -- Use the in-tree identification chain (mirrors chip 19l's proof):
  -- pmat k₀ i₀ = lam₁ and pmat k₁ i₀ = lam₂.
  have h_cg_0 :
      (sb.reindex hg).cycleGens k₀ = sb.cycleGens ⟨0, by decide⟩ := by
    rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
    congr 1
  have h_cg_1 :
      (sb.reindex hg).cycleGens k₁ = sb.cycleGens ⟨1, by decide⟩ := by
    rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
    congr 1
  have h_basis : basis_g_dz L i₀ = dz L := by
    rw [basis_g_dz_apply]
    rw [show finCongr (genus_eq_one L) i₀ = (0 : Fin 1) from Subsingleton.elim _ _]
    exact basis_one_dz_apply L
  have h_pp_0 :
      PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (sb.cycleGens ⟨0, by decide⟩) (dz L)
        = lam₁ := by
    rw [PeriodPairing_ofSmoothCycle]
    have h_cycle_eq : sb.cycleGens ⟨0, by decide⟩
        = single_smoothLoop_smoothCycle (torusBasisLoop lam₁ hlam₁)
            ((torusBasisLoop_src lam₁ hlam₁).trans
              (torusBasisLoop_tgt lam₁ hlam₁).symm) := by
      apply Subtype.ext
      simp only [SmoothSymplecticBasis.cycleGens_coe]
      rw [single_smoothLoop_smoothCycle_coe]
      rfl
    rw [h_cycle_eq]
    exact complexPeriod_torusBasisLoop_dz L lam₁ hlam₁
  have h_pp_1 :
      PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (sb.cycleGens ⟨1, by decide⟩) (dz L)
        = lam₂ := by
    rw [PeriodPairing_ofSmoothCycle]
    have h_cycle_eq : sb.cycleGens ⟨1, by decide⟩
        = single_smoothLoop_smoothCycle (torusBasisLoop lam₂ hlam₂)
            ((torusBasisLoop_src lam₂ hlam₂).trans
              (torusBasisLoop_tgt lam₂ hlam₂).symm) := by
      apply Subtype.ext
      simp only [SmoothSymplecticBasis.cycleGens_coe]
      rw [single_smoothLoop_smoothCycle_coe]
      rfl
    rw [h_cycle_eq]
    exact complexPeriod_torusBasisLoop_dz L lam₂ hlam₂
  -- The period matrix entries match.
  have h_pm_0 :
      periodMatrix (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens) k₀ i₀ = lam₁ := by
    show PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
      ((sb.reindex hg).cycleGens k₀) (basis_g_dz L i₀) = lam₁
    rw [h_cg_0, h_basis, h_pp_0]
  have h_pm_1 :
      periodMatrix (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens) k₁ i₀ = lam₂ := by
    show PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
      ((sb.reindex hg).cycleGens k₁) (basis_g_dz L i₀) = lam₂
    rw [h_cg_1, h_basis, h_pp_1]
  rw [h_pm_0, h_pm_1]
  exact h_orient

end ComplexTorus

end JacobianChallenge

end
