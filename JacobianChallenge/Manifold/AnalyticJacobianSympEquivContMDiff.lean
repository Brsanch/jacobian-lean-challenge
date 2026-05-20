/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointHomeomorphComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeMkQContMDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `analyticJacobianSympEquiv_complexTorus` is `ContMDiff`

The inverse direction of the homeomorphism `ℂ⧸L ≃ₜ AnalyticJacobianSymp`
is smooth. Proof structure parallel to `abelJacobiPoint_contMDiff`:

* For each `v ∈ AnalyticJacobianSymp`, pick a chart which provides a
  smooth lift `w := chartAt v` ∈ `Fin g → ℂ`.
* `analyticJacobianSympEquiv v = mkQ_L (funUnique w)` on the chart
  source (by `QuotientAddGroup.congr` on `mkQ_AJ ∘ chartAt = id`).
* Composition `chartAt + funUniqueAddEquivComplexTorus + mkQ_L` is smooth.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness of `analyticJacobianSympEquiv_complexTorus` -/

/-- **`analyticJacobianSympEquiv_complexTorus` is `ContMDiff`.** -/
theorem analyticJacobianSympEquiv_contMDiff
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
    ContMDiff 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) 𝓘(ℂ, ℂ) ω
      (analyticJacobianSympEquiv_complexTorus L h
        : AnalyticJacobianSymp _ (basis_g_dz L) h → ℂ ⧸ L) := by
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
  letI hCS : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toChartedSpace
  letI : IsManifold 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
      (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toIsManifold
  apply contMDiff_of_locally_contMDiffOn
  intro v₀
  refine ⟨(chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀).source,
    (chartAt _ v₀).open_source, mem_chart_source _ v₀, ?_⟩
  -- The chart map is ContMDiffOn.
  have h_chart_smooth :
      ContMDiffOn 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
        𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
        (chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀
          : AnalyticJacobianSymp _ (basis_g_dz L) h →
            Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
        (chartAt _ v₀).source :=
    contMDiffOn_chart
  -- funUniqueAddEquivComplexTorus is ContMDiff (continuous ℝ-linear).
  have h_funUnique_smooth :
      ContMDiff 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) 𝓘(ℂ, ℂ) ω
        (funUniqueAddEquivComplexTorus L
          : (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) → ℂ) := by
    -- The function is `f ↦ f (default : Fin (genus T_L))` via uniqueFinGenus.
    -- Use `contDiff_apply` at that specific default index.
    letI : Unique (Fin (JacobianChallenge.genus (ℂ ⧸ L))) := uniqueFinGenus L
    have h_eq :
        (funUniqueAddEquivComplexTorus L
          : (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) → ℂ)
          = (fun f : Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ => f default) :=
      funext (funUniqueAddEquivComplexTorus_apply L)
    rw [h_eq]
    exact (contDiff_apply ℂ ℂ default).contMDiff
  -- mkQ_L is ContMDiff.
  have h_mkQ_smooth : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (L.mkQ : ℂ → ℂ ⧸ L) := mkQ_contMDiff L ω
  -- Composition.
  have h_comp_smooth :
      ContMDiffOn 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) 𝓘(ℂ, ℂ) ω
        (fun v : AnalyticJacobianSymp _ (basis_g_dz L) h =>
          L.mkQ (funUniqueAddEquivComplexTorus L
            (chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀ v)))
        (chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀).source := by
    have h_step1 :
        ContMDiffOn 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) 𝓘(ℂ, ℂ) ω
          (fun v : AnalyticJacobianSymp _ (basis_g_dz L) h =>
            funUniqueAddEquivComplexTorus L
              (chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀ v))
          (chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀).source :=
      h_funUnique_smooth.comp_contMDiffOn h_chart_smooth
    exact h_mkQ_smooth.comp_contMDiffOn h_step1
  -- analyticJacobianSympEquiv = mkQ_L ∘ funUnique ∘ chartAt on chart source.
  refine h_comp_smooth.congr ?_
  intro v hv
  -- mkQ_AJ (chartAt v) = v on chart source.
  have h_lift : (QuotientAddGroup.mk
      (chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀ v)
      : (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ⧸
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h).lattice) = v := by
    have h_chart_apply :=
      (localChart (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h).lattice.toIntSubmodule
            (discRadius_separates _) v₀.out).right_inv hv
    exact h_chart_apply
  -- Use chartAt v₀ v as the lift.
  set w := chartAt (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) v₀ v with hw
  -- Both sides are functions of w; rewrite the LHS via h_lift then use defeq.
  show analyticJacobianSympEquiv_complexTorus L h v = L.mkQ (funUniqueAddEquivComplexTorus L w)
  conv_lhs => rw [← h_lift]
  rfl

end ComplexTorus

end JacobianChallenge

end
