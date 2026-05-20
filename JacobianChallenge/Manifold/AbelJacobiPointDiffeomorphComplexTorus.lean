/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointHomeomorphComplexTorus
import JacobianChallenge.Manifold.AnalyticJacobianSympEquivContMDiff
import Mathlib.Geometry.Manifold.Diffeomorph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `ℂ⧸L ≃ₘ AnalyticJacobianSymp` — smooth diffeomorphism

Both directions of the bijection are `ContMDiff`, so we package the
classical AJ-point map as a smooth diffeomorphism between `T_L` and
`AnalyticJacobianSymp`.

This is the strongest form of the structural identification: T_L IS
AnalyticJacobianSymp as smooth complex manifolds (genus-1 surface).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The smooth diffeomorphism `ℂ⧸L ≃ₘ AnalyticJacobianSymp`.**

Composes the unconditional `abelJacobiPointEquiv` with both directions
of `ContMDiff` (forward via `abelJacobiPoint_contMDiff`, inverse via
`analyticJacobianSympEquiv_contMDiff`). -/
noncomputable def abelJacobiPointDiffeomorph
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    haveI : DiscreteTopology
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
    haveI : IsZLattice ℝ
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h).lattice.toIntSubmodule :=
      PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
    letI : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
        (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h) :=
      (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toChartedSpace
    Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
      (ℂ ⧸ L) (AnalyticJacobianSymp _ (basis_g_dz L) h) ω := by
  haveI : DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
  haveI : IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h).lattice.toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
  letI : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toChartedSpace
  letI : IsManifold 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toIsManifold
  refine
    { toEquiv := (abelJacobiPointEquiv L h).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · -- Forward: abelJacobiPoint is ContMDiff.
    exact abelJacobiPoint_contMDiff L h
  · -- Inverse: analyticJacobianSympEquiv is ContMDiff.
    -- The inverse of abelJacobiPointEquiv is analyticJacobianSympEquiv
    -- (by abelJacobiPointEquiv_eq_symm).
    have h_inv : (abelJacobiPointEquiv L h).toEquiv.symm
        = (analyticJacobianSympEquiv_complexTorus L h).toEquiv := by
      have := abelJacobiPointEquiv_eq_symm L h
      rw [this]
      rfl
    rw [h_inv]
    exact analyticJacobianSympEquiv_contMDiff L h

end ComplexTorus

end JacobianChallenge

end
