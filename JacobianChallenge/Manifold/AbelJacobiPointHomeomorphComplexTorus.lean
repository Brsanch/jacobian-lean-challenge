/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointAdditiveComplexTorus
import JacobianChallenge.Manifold.AbelJacobiSmoothnessComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasicInstances

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `abelJacobiPoint` is a homeomorphism on T_L (unconditional)

Combines:
* `abelJacobiPointEquiv` (the unconditional AddEquiv).
* `abelJacobiPoint_contMDiff` (smoothness, hence continuity).
* `CompactSpace (ℂ ⧸ L)` (in tree).
* `T2Space AnalyticJacobianSymp` (in tree via `JacobianOfLattice.instT2Space`).

By `Continuous.homeoOfEquivCompactToT2`, a continuous bijection from a
compact space to a T2 space is a homeomorphism. Hence
`ℂ ⧸ L ≃ₜ AnalyticJacobianSymp` unconditionally.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`ℂ ⧸ L ≃ₜ AnalyticJacobianSymp` via the AJ point map.**
Unconditional. -/
noncomputable def abelJacobiPointHomeomorph
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    haveI : T2Space (AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h) :=
        haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
        haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
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
        JacobianOfLattice.instT2Space _
    (ℂ ⧸ L) ≃ₜ AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h := by
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
  haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
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
  haveI hT2 : T2Space (AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h) :=
    JacobianOfLattice.instT2Space _
  letI hCS : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h)).toChartedSpace
  letI : IsManifold 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h)).toIsManifold
  -- Continuity of abelJacobiPoint via the ContMDiff smoothness.
  have h_cont : Continuous (abelJacobiPointEquiv L h : ℂ ⧸ L →
      AnalyticJacobianSymp _ (basis_g_dz L) h) :=
    (abelJacobiPoint_contMDiff L h).continuous
  exact Continuous.homeoOfEquivCompactToT2 (f := (abelJacobiPointEquiv L h).toEquiv)
    h_cont

end ComplexTorus

end JacobianChallenge

end
