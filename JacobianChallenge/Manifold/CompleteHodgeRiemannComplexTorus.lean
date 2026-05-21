/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannGenusOneOrientation
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus
import JacobianChallenge.Manifold.ComplexTorusRiemannBilinear

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` on the complex torus `T_L = ℂ ⧸ L` (chip 19l)

Concrete classical content: on the complex torus
`T_L = ℂ ⧸ L`, with a chosen pair of lattice generators
`(lam₁, lam₂) ∈ L` and the lattice-orientation condition
`0 < Im(star lam₁ · lam₂)`, the full `CompleteHodgeRiemannHypothesis`
holds for the data `(PeriodPairingData.ofSmoothCycle, basis_g_dz,
((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex (genus_eq_one L)).cycleGens)`.

This is the **first concrete non-trivial instantiation** of the chip 19
arc on a genus-1 manifold. Combined with the subsingleton-ω genus-0
case (`completeHodgeRiemannHypothesis_of_subsingleton`), it validates
the new Hodge–Riemann chain on the two canonical examples (RS at genus
0, T_L at genus 1).

The proof composes:

* `completeHodgeRiemannHypothesis_genus_one_of_orientation` (chip 19k),
* identification of cycleGens through the symplectic basis (via
  `reindex_cycleGens_apply`),
* identification of `basis_g_dz L` value at the unique basis index via
  `basis_g_dz_apply` + Subsingleton elim,
* `complexPeriod_torusBasisLoop_dz` (period = lattice generator).

## What this file ships

* `completeHodgeRiemannHypothesis_complexTorus` — the T_L application.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Matrix

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`CompleteHodgeRiemannHypothesis` on `T_L = ℂ ⧸ L`** from a
lattice-orientation input. Validates the full chip 19 chain on a
concrete genus-1 manifold.

The single classical input is `0 < (star lam₁ · lam₂).im`, the
standard "positive area" condition on the lattice basis. -/
theorem completeHodgeRiemannHypothesis_complexTorus
    (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L)
    (h_orient : 0 < (star lam₁ * lam₂).im) :
    CompleteHodgeRiemannHypothesis
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
      (basis_g_dz L)
      (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
        (genus_eq_one L)).cycleGens) := by
  have hg : JacobianChallenge.genus (ℂ ⧸ L) = 1 := genus_eq_one L
  have h2g : 0 < 2 * JacobianChallenge.genus (ℂ ⧸ L) := by rw [hg]; decide
  have h2g' : 1 < 2 * JacobianChallenge.genus (ℂ ⧸ L) := by rw [hg]; decide
  have hg' : 0 < JacobianChallenge.genus (ℂ ⧸ L) := by rw [hg]; decide
  -- Construct explicit cycle / basis indices.
  set k₀ : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) := ⟨0, h2g⟩ with hk0_def
  set k₁ : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) := ⟨1, h2g'⟩ with hk1_def
  set i₀ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) := ⟨0, hg'⟩ with hi0_def
  -- Apply chip 19k.
  refine completeHodgeRiemannHypothesis_genus_one_of_orientation
    hg k₀ k₁ rfl rfl i₀ ?_
  -- Goal: 0 < Im(star (PP cycleGens k₀ i₀) · PP cycleGens k₁ i₀)
  -- Reduce to: 0 < Im(star lam₁ · lam₂).
  -- Step 1: identify cycleGens k₀ and k₁ on T_L's reindexed symplectic basis.
  set sb := symplecticBasis L lam₁ lam₂ hlam₁ hlam₂
  -- (sb.reindex hg).cycleGens k = sb.cycleGens (Fin.cast _ k) (by reindex_cycleGens_apply)
  -- Fin.cast on k₀ = ⟨0, _⟩ : Fin (2 * 1) (i.e., Fin 2) gives ⟨0, _⟩.
  have h_cg_0 :
      (sb.reindex hg).cycleGens k₀ = sb.cycleGens ⟨0, by decide⟩ := by
    rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
    congr 1
  have h_cg_1 :
      (sb.reindex hg).cycleGens k₁ = sb.cycleGens ⟨1, by decide⟩ := by
    rw [SmoothSymplecticBasis.reindex_cycleGens_apply]
    congr 1
  -- Step 2: basis_g_dz L i₀ = dz L.
  have h_basis : basis_g_dz L i₀ = dz L := by
    rw [basis_g_dz_apply]
    rw [show finCongr (genus_eq_one L) i₀ = (0 : Fin 1) from Subsingleton.elim _ _]
    exact basis_one_dz_apply L
  -- Step 3: PeriodPairing data sb.cycleGens ⟨0, _⟩ (dz L) = lam₁.
  -- sb.cycleGens ⟨0, _⟩ = single_smoothLoop_smoothCycle (torusBasisLoop lam₁ hlam₁) _.
  have h_pp_0 :
      PeriodPairing (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (sb.cycleGens ⟨0, by decide⟩) (dz L)
        = lam₁ := by
    rw [PeriodPairing_ofSmoothCycle]
    -- sb.cycleGens ⟨0, _⟩ = single_smoothLoop_smoothCycle (sb.basis ⟨0, _⟩) _
    --                    = single_smoothLoop_smoothCycle (torusBasisLoop lam₁ _) _
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
  -- Combine.
  rw [h_cg_0, h_cg_1, h_basis, h_pp_0, h_pp_1]
  exact h_orient

end ComplexTorus

end JacobianChallenge

end
