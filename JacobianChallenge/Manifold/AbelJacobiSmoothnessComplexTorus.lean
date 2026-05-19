/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeImageComplexTorusReverse
import JacobianChallenge.Manifold.PeriodLatticeMkQContMDiff
import JacobianChallenge.Manifold.C3FullInputExtSymp

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `AbelJacobiSmoothnessSymp` on T_L, unconditional

Closes the second of the four open classical hypotheses on
`T_L = ℂ ⧸ L`. The Abel-Jacobi point map is smooth via:

1. The explicit formula `abelJacobiPoint Q = [fun _ => Q.out]`.
2. The lattice characterization
   `(fun _ => z) ∈ periodLatticeImage ↔ z ∈ L`.
3. Two different lifts of the same `Q : T_L` differ by an element of
   `L`, hence give the same `[fun _ => …]` class.
4. The chart `chartAt ℂ Q₀` provides a smooth lift over a
   neighborhood.

Concretely: over `(chartAt ℂ Q₀).source`, the map
`abelJacobiPoint = mkQ_AJ ∘ constFin ∘ chartAt`, a composition of
three smooth maps. Globally smooth by `contMDiff_of_locally_contMDiffOn`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Two-lift coincidence in `AnalyticJacobianSymp` -/

/-- **If two points of `ℂ` project to the same point of `T_L`, their
constant-function lifts give the same class in `AnalyticJacobianSymp`.** -/
theorem const_eq_in_analyticJacobianSymp
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    {z₁ z₂ : ℂ} (hmk : L.mkQ z₁ = L.mkQ z₂) :
    (QuotientAddGroup.mk (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₁)
        : AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) h)
      = QuotientAddGroup.mk (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₂) := by
  -- mk z₁ = mk z₂ in T_L ⇔ z₁ - z₂ ∈ L.
  have h_diff_in_L : z₁ - z₂ ∈ L := by
    have : (L.mkQ : ℂ → ℂ ⧸ L) (z₁ - z₂) = 0 := by
      rw [map_sub, hmk, sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  -- (fun _ => z₁) - (fun _ => z₂) = fun _ => z₁ - z₂ ∈ periodLatticeImage.
  have h_pt :
      (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₁)
        - (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₂)
      = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₁ - z₂ := by
    funext _; rfl
  have h_in_image :
      (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₁ - z₂)
        ∈ periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) :=
    const_mem_periodLatticeImage_of_mem_L L _ h_diff_in_L
  -- mk in AnalyticJacobianSymp respects the periodLatticeImage subgroup,
  -- hence equal class.
  apply (QuotientAddGroup.eq).mpr
  rw [PeriodLatticeOfRankTwoG.ofSymplectic_lattice]
  -- Goal: -(fun _ => z₁) + (fun _ => z₂) ∈ periodLatticeImage.
  -- This equals -(z₁ - z₂) constantly = -(z₁ - z₂) ∈ L, in L iff (z₁ - z₂) ∈ L.
  have h_neg_in_L : -(z₁ - z₂) ∈ L := L.neg_mem h_diff_in_L
  have h_neg :
      -(fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₁)
        + (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => z₂)
      = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => -(z₁ - z₂) := by
    funext _; show -z₁ + z₂ = -(z₁ - z₂); ring
  rw [h_neg]
  exact const_mem_periodLatticeImage_of_mem_L L _ h_neg_in_L

/-! ## Smoothness of the building blocks -/

/-- **`constFin : ℂ → (Fin n → ℂ)` is a continuous ℂ-linear map** (hence
ContMDiff). -/
noncomputable def constFinCLM (n : ℕ) : ℂ →L[ℂ] (Fin n → ℂ) where
  toFun z := fun _ => z
  map_add' z₁ z₂ := by funext _; rfl
  map_smul' c z := by funext _; rfl
  cont := continuous_pi (fun _ : Fin n => continuous_id)

@[simp] lemma constFinCLM_apply (n : ℕ) (z : ℂ) (i : Fin n) :
    constFinCLM n z i = z := rfl

/-- **`constFinCLM` is ContMDiff**. -/
theorem constFinCLM_contMDiff (n : ℕ) (k : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin n → ℂ) k (constFinCLM n : ℂ → Fin n → ℂ) :=
  (constFinCLM n).contDiff.contMDiff

/-! ## Local smoothness of `abelJacobiPoint` on chart sources -/

/-- **On `(chartAt ℂ Q₀).source`, `abelJacobiPoint` equals
`mkQ_AJ ∘ constFinCLM ∘ chartAt`.** -/
private lemma abelJacobiPoint_eq_on_chart
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (Q₀ : ℂ ⧸ L) :
    Set.EqOn
      ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint
        : ℂ ⧸ L → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) h)
      (fun Q : ℂ ⧸ L =>
        (QuotientAddGroup.mk
            ((constFinCLM (JacobianChallenge.genus (ℂ ⧸ L)) (chartAt ℂ Q₀ Q) :
              Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ))
          : AnalyticJacobianSymp _ (basis_g_dz L) h))
      (chartAt ℂ Q₀).source := by
  intro Q hQ
  rw [canonicalAbelJacobiInputSymp_abelJacobiPoint]
  -- Goal: [fun _ => Q.out] = [fun _ => chartAt Q].
  -- Need: mkQ (chartAt Q) = mkQ Q.out (both lift Q).
  -- chartAt Q ∈ chart-target which is preimage of chart-source under mkQ.
  -- For our T_L: chartAt is (localChart _ Q₀.out).symm, and applying it
  -- maps Q to a point z with mkQ z = Q.
  have h_mk_chart : L.mkQ (chartAt ℂ Q₀ Q) = Q := by
    -- chartAt ℂ Q₀ = (localChart L _ Q₀.out).symm.
    -- For Q in target of localChart.symm (which is source of localChart),
    -- (localChart.symm).toFun Q = localChart.invFun Q. And localChart's
    -- partial-homeo property gives `localChart (localChart.invFun Q) = Q`,
    -- i.e., mkQ (localChart.invFun Q) = Q on the chart-source-of-symm.
    have h_eq_chart : chartAt ℂ Q₀ Q
        = (localChart L (discRadius_separates L) Q₀.out).symm Q := rfl
    rw [h_eq_chart]
    -- Apply localChart's `.right_inv` (or `.symm.left_inv`) at Q.
    have h_in_target : Q ∈
        (localChart L (discRadius_separates L) Q₀.out).target := hQ
    -- localChart applied to its inverse value gives back Q.
    have h_chart_apply :=
      (localChart L (discRadius_separates L) Q₀.out).right_inv h_in_target
    -- h_chart_apply : (localChart L _ Q₀.out)
    --   ((localChart L _ Q₀.out).symm Q) = Q.
    -- Now use that localChart's forward equals mkQ on its source.
    have h_symm_in_src : (localChart L (discRadius_separates L) Q₀.out).symm Q
        ∈ (localChart L (discRadius_separates L) Q₀.out).source :=
      (localChart L (discRadius_separates L) Q₀.out).symm.mapsTo h_in_target
    have h_forward_eq_mkQ :
        (localChart L (discRadius_separates L) Q₀.out)
            ((localChart L (discRadius_separates L) Q₀.out).symm Q)
          = L.mkQ ((localChart L (discRadius_separates L) Q₀.out).symm Q) := rfl
    rw [h_forward_eq_mkQ] at h_chart_apply
    exact h_chart_apply
  -- mkQ Q.out = Q always.
  have h_mk_out : L.mkQ Q.out = Q := by
    show (Quotient.mk'' Q.out : ℂ ⧸ L) = Q
    exact Quotient.out_eq Q
  -- Both are lifts of Q, so equal in AnalyticJacobianSymp.
  -- The `constFinCLM` is definitionally `fun _ => chartAt Q`.
  show (QuotientAddGroup.mk (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q.out)
        : AnalyticJacobianSymp _ (basis_g_dz L) h)
    = QuotientAddGroup.mk (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) =>
        chartAt ℂ Q₀ Q)
  exact const_eq_in_analyticJacobianSymp L h
    (h_mk_out.trans h_mk_chart.symm)

/-! ## Headline: `abelJacobiPoint` is ContMDiff -/

/-- **`abelJacobiPoint` on the canonical AJ input is ContMDiff.**
Achieved via local-on-chart smoothness combined globally. -/
theorem abelJacobiPoint_contMDiff
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
    haveI : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
        (AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h) :=
      (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds _).toChartedSpace
    ContMDiff 𝓘(ℂ, ℂ)
      𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
      ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint
        : ℂ ⧸ L → AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L) h) := by
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
  -- Also under the bare `periodLatticeImage` form for `mkQ_contMDiff_complex`.
  haveI : DiscreteTopology
      (periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)).toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle h
  haveI : IsZLattice ℝ
      (periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L)).toIntSubmodule :=
    PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h
  letI : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
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
  -- The same instances under the unfolded `JacobianOfLattice` form.
  letI : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
      (JacobianOfLattice (ℂ ⧸ L)
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h)) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h)).toChartedSpace
  letI : IsManifold 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
      (JacobianOfLattice (ℂ ⧸ L)
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h)) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h)).toIsManifold
  -- And under the fully-unfolded `(Fin g → ℂ) ⧸ data.lattice` form.
  letI : ChartedSpace (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
      ((Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ⧸
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h).lattice) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h)).toChartedSpace
  letI : IsManifold 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
      ((Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ⧸
        (PeriodLatticeOfRankTwoG.ofSymplectic
          (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
          (basis_g_dz L) h).lattice) :=
    (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
        (basis_g_dz L) h)).toIsManifold
  apply contMDiff_of_locally_contMDiffOn
  intro Q₀
  refine ⟨(chartAt ℂ Q₀).source, (chartAt ℂ Q₀).open_source,
    mem_chart_source _ Q₀, ?_⟩
  -- ContMDiffOn ... on chart source.
  have h_chart_smooth :
      ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        (chartAt ℂ Q₀ : ℂ ⧸ L → ℂ) (chartAt ℂ Q₀).source :=
    contMDiffOn_chart
  -- The composition mkQ_AJ ∘ constFinCLM is smooth.
  have h_const_smooth :
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
        (constFinCLM (JacobianChallenge.genus (ℂ ⧸ L))
          : ℂ → Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) :=
    constFinCLM_contMDiff _ ω
  have h_mkQ_smooth :
      ContMDiff 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
        𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
        ((periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
            (basis_g_dz L)).toIntSubmodule.mkQ
          : (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
            → (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ)
                ⧸ (periodLatticeImage (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
                  (basis_g_dz L)).toIntSubmodule) :=
    mkQ_contMDiff_complex _ ω
  -- The composition is the post-mk-AJ map applied to constFinCLM(chartAt Q).
  have h_comp_smooth :
      ContMDiffOn 𝓘(ℂ, ℂ)
        𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
        (fun Q : ℂ ⧸ L =>
          (QuotientAddGroup.mk
              (constFinCLM (JacobianChallenge.genus (ℂ ⧸ L)) (chartAt ℂ Q₀ Q))
            : AnalyticJacobianSymp _ (basis_g_dz L) h))
        (chartAt ℂ Q₀).source := by
    have h_step1 :
        ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ω
          (fun Q : ℂ ⧸ L =>
            constFinCLM (JacobianChallenge.genus (ℂ ⧸ L)) (chartAt ℂ Q₀ Q))
          (chartAt ℂ Q₀).source :=
      h_const_smooth.comp_contMDiffOn h_chart_smooth
    exact h_mkQ_smooth.comp_contMDiffOn h_step1
  -- Use the chart-equality lemma to transport.
  exact (h_comp_smooth).congr (abelJacobiPoint_eq_on_chart L h Q₀)

/-! ## Discharge of `AbelJacobiSmoothnessSymp` -/

/-- **`AbelJacobiSmoothnessSymp` on the canonical AJ input is
unconditional on T_L.** -/
theorem abelJacobiSmoothness_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
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
    AbelJacobiSmoothnessSymp (canonicalAbelJacobiInputSymp L h) := by
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
  -- The predicate `AbelJacobiSmoothnessSymp` is a `ContMDiff` claim on
  -- `abelJacobiPoint` (modulo a `haveI` chartedSpace setup). Pass through
  -- to our headline `abelJacobiPoint_contMDiff`.
  exact abelJacobiPoint_contMDiff L h

end ComplexTorus

end JacobianChallenge

end
