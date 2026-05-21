/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CompleteHodgeRiemannComplexTorusUnconditional
import JacobianChallenge.Manifold.BilinearFromHodgeChain

set_option linter.unusedSectionVars false

/-! # `RiemannBilinearRelations` on `T_L` UNCONDITIONAL (chip 20l)

Composes:

* chip 19t (`exists_completeHodgeRiemannHypothesis_complexTorus`):
  `CompleteHodgeRiemannHypothesis` on `T_L` for some explicit
  `(lam₁, lam₂)` symplectic basis;
* `realLI_periodVector_of_completeHodgeRiemann` (chip 3) — extracts
  ℝ-LI of period vectors from CHRH.

Both `RiemannBilinearRelations` (the `∃ J, first ∧ second` bundle)
and the ℝ-LI of period vectors on `T_L` follow unconditionally,
without any orientation hypothesis on the lattice.

## What this file ships

* `exists_riemannBilinearRelations_complexTorus` — `Nonempty`-form
  RBR on T_L with the basis_g_dz / reindexed symplectic basis from
  chip 19t's witness.
* `exists_realLI_periodVector_complexTorus` — `Nonempty`-form ℝ-LI
  of period vectors on T_L (the SmoothHomologyDataPackage `bilinear`
  field).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`RiemannBilinearRelations` on `T_L` UNCONDITIONAL.**

The `∃ J, first ∧ second` bundle holds on T_L for the `basis_g_dz`
basis and a symplectic basis from chip 19t's adaptively-chosen
positively-oriented lattice pair. -/
theorem exists_riemannBilinearRelations_complexTorus :
    ∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),
      RiemannBilinearRelations
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)
        (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
          (genus_eq_one L)).cycleGens) := by
  obtain ⟨lam₁, lam₂, hlam₁, hlam₂, hCHRH⟩ :=
    exists_completeHodgeRiemannHypothesis_complexTorus L
  obtain ⟨J, H, hPD, hFirst, hBridge⟩ := hCHRH
  exact ⟨lam₁, lam₂, hlam₁, hlam₂,
    RiemannBilinearRelations_of_HodgeBridge_and_first hPD hBridge hFirst⟩

/-- **ℝ-LI of period vectors on `T_L` UNCONDITIONAL (CHRH-derived form).**

Parallel discharge of the `bilinear` field of
`SmoothHomologyDataPackage` via the chip 19r/t CHRH chain. Already
covered by the in-tree `riemannBilinear_transport` +
`basisFin2OfL_realLinearIndependent` route — this is the
alternative-route derivation through the new chip 19/20 chain. -/
theorem exists_realLI_periodVector_complexTorus :
    ∃ (lam₁ lam₂ : ℂ) (hlam₁ : lam₁ ∈ L) (hlam₂ : lam₂ ∈ L),
      LinearIndependent ℝ
        (fun i : Fin (2 * JacobianChallenge.genus (ℂ ⧸ L)) =>
          periodVector (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L)
            (((symplecticBasis L lam₁ lam₂ hlam₁ hlam₂).reindex
              (genus_eq_one L)).cycleGens i)) := by
  obtain ⟨lam₁, lam₂, hlam₁, hlam₂, hCHRH⟩ :=
    exists_completeHodgeRiemannHypothesis_complexTorus L
  exact ⟨lam₁, lam₂, hlam₁, hlam₂,
    realLI_periodVector_of_completeHodgeRiemann hCHRH⟩

end ComplexTorus

end JacobianChallenge

end
