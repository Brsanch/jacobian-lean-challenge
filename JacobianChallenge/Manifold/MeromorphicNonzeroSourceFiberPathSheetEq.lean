/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLevelSetChain
import JacobianChallenge.Manifold.MeromorphicNonzeroPathLiftUniqueOnContinuousOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Local identification of `sourceFiberPath` with `sheet.g ∘ β ∘ σ`

For `f : MeromorphicNonzero X` non-constant and a fiber point `x` over
`β 0` with `x ∈ regularSet`, the local-sheet `LocalSheetData` centered
at `x` provides a continuous local inverse `sheet.g : RiemannSphere →
X`. The `Classical.choose`-defined `sourceFiberPath ...` is in
principle related to `sheet.g ∘ β ∘ Real.smoothTransition` (the
"obvious" lift), but the existing infrastructure only exposes the
properties of `sourceFiberPath` opaquely via `choose_spec`.

This file makes the relationship explicit on a sub-interval `[0, δ]`
where both `(sourceFiberPath p).toPath.extend t ∈ sheet.U` and
`β(σ t) ∈ sheet.V`. The proof composes:

* The two paths agree at `t = 0` (both equal `x`).
* Both lift `β ∘ Real.smoothTransition` on `[0, δ]`.
* On `[0, δ]`, both are continuous (one globally via `Path.extend`,
  one via `ContinuousOn` of `sheet.g` on `sheet.V` plus
  `β ∘ σ` mapping `[0, δ]` to `sheet.V`).
* Apply `path_lift_eqOn_Icc_of_continuousOn`
  (`MeromorphicNonzeroPathLiftUniqueOnContinuousOn.lean`) to conclude
  pointwise equality on `[0, δ]`.

This is the **local identification chip**. The global identification
on `[0, 1]` requires a subdivision over a finite open cover of the
β-trace by sheet domains, which is a separate downstream chip.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff unitInterval

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Local identification of `sourceFiberPath p`'s lift with the
explicit sheet pullback.**

For `f : MeromorphicNonzero X` non-constant, a smooth `β : ℝ →
RiemannSphere` regular on `[0, 1]`, a fiber point `x` over `β 0`, and
the local sheet centered at `x`, there exists `δ ∈ (0, 1]` such that
`(sourceFiberPath p).toPath.extend t = sheet.g (β (σ t))` for every
`t ∈ [0, δ]`.

The sub-interval `[0, δ]` is chosen so that:

* `β (σ t) ∈ sheet.V` (sheet's target neighborhood of `β 0 = f x`),
  by continuity of `β ∘ σ` at `0`.
* `(sourceFiberPath p).toPath.extend t ∈ sheet.U` (sheet's source
  neighborhood of `x`), by continuity of `toPath.extend` at `0`.

On this interval, both functions lift `β ∘ σ` and agree at `t = 0`,
so they agree everywhere by
`path_lift_eqOn_Icc_of_continuousOn`. -/
theorem sourceFiberPath_toPath_extend_eq_sheet_g_locally
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0:ℝ) 1, β t ∈ f.regularValueSet)
    {x : X} (hx : f.toRiemannSphere x = β 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ t ∈ Icc (0 : ℝ) δ,
        (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t
          = (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx)).g
              (β (Real.smoothTransition t)) := by
  classical
  -- Abbreviations.
  set hx_reg : x ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue
      (hβ_reg 0 ⟨le_refl _, by norm_num⟩) hx with hx_reg_def
  set sheet := f.localSheetData_at_regular hnc hx_reg
  set γ₁ : ℝ → X := fun t => (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t
    with hγ₁_def
  set γ₂ : ℝ → X := fun t => sheet.g (β (Real.smoothTransition t)) with hγ₂_def
  -- Step 1: Continuity of γ₁ (global, from Path.extend).
  have hγ₁_cont : Continuous γ₁ :=
    (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.continuous_extend
  -- Step 2: β ∘ σ is continuous (β continuous + σ continuous).
  have hβσ_cont : Continuous (fun t : ℝ => β (Real.smoothTransition t)) := by
    refine hβ_smooth.continuous.comp ?_
    exact Real.smoothTransition.continuous
  -- Step 3: β 0 ∈ sheet.V.
  have hβ0_in_V : β 0 ∈ sheet.V := by
    show β 0 ∈ (f.manifoldLocalOph hnc hx_reg).target
    rw [← hx]
    have hx_src : x ∈ (f.manifoldLocalOph hnc hx_reg).source :=
      f.mem_source_manifoldLocalOph hnc hx_reg
    rw [← f.manifoldLocalOph_apply hnc hx_reg hx_src]
    exact (f.manifoldLocalOph hnc hx_reg).map_source hx_src
  -- Step 4: x ∈ sheet.U.
  have hx_in_U : x ∈ sheet.U := f.mem_source_manifoldLocalOph hnc hx_reg
  -- Step 5: γ₂ is continuous on the preimage `(β ∘ σ) ⁻¹' sheet.V`.
  have hsheet_g_contOn : ContinuousOn sheet.g sheet.V := sheet.g_continuousOn
  have hβσ_preV_open : IsOpen ((fun t : ℝ => β (Real.smoothTransition t))
      ⁻¹' sheet.V) :=
    hβσ_cont.isOpen_preimage _ sheet.V_open
  have h0_in_preV : (0 : ℝ) ∈ (fun t : ℝ => β (Real.smoothTransition t))
      ⁻¹' sheet.V := by
    simp only [Set.mem_preimage, Real.smoothTransition.zero]
    exact hβ0_in_V
  -- δ₁ such that [0, δ₁] ⊆ (β∘σ) ⁻¹' sheet.V.
  obtain ⟨δ₁, hδ₁_pos, hδ₁_sub⟩ : ∃ δ : ℝ, 0 < δ ∧
      Icc (0 : ℝ) δ ⊆ (fun t : ℝ => β (Real.smoothTransition t)) ⁻¹' sheet.V := by
    have h_nhds : (fun t : ℝ => β (Real.smoothTransition t)) ⁻¹' sheet.V
        ∈ 𝓝 (0 : ℝ) :=
      hβσ_preV_open.mem_nhds h0_in_preV
    rw [Metric.mem_nhds_iff] at h_nhds
    obtain ⟨ε, hε_pos, hε_sub⟩ := h_nhds
    refine ⟨ε / 2, by linarith, ?_⟩
    intro t ⟨ht0, ht_le⟩
    apply hε_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith
  -- δ₂ such that [0, δ₂] ⊆ γ₁ ⁻¹' sheet.U.
  have hγ₁0 : γ₁ 0 = x := by
    show (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend 0 = x
    rw [Path.extend_zero]
    exact f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx
  have hγ₁_preU_open : IsOpen (γ₁ ⁻¹' sheet.U) :=
    hγ₁_cont.isOpen_preimage _ sheet.U_open
  have h0_in_preU : (0 : ℝ) ∈ γ₁ ⁻¹' sheet.U := by
    simp only [Set.mem_preimage, hγ₁0]
    exact hx_in_U
  obtain ⟨δ₂, hδ₂_pos, hδ₂_sub⟩ : ∃ δ : ℝ, 0 < δ ∧
      Icc (0 : ℝ) δ ⊆ γ₁ ⁻¹' sheet.U := by
    have h_nhds : γ₁ ⁻¹' sheet.U ∈ 𝓝 (0 : ℝ) :=
      hγ₁_preU_open.mem_nhds h0_in_preU
    rw [Metric.mem_nhds_iff] at h_nhds
    obtain ⟨ε, hε_pos, hε_sub⟩ := h_nhds
    refine ⟨ε / 2, by linarith, ?_⟩
    intro t ⟨ht0, ht_le⟩
    apply hε_sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith
  -- δ := min (min δ₁ δ₂) 1.
  set δ : ℝ := min (min δ₁ δ₂) 1 with hδ_def
  have hδ_pos : 0 < δ := lt_min (lt_min hδ₁_pos hδ₂_pos) (by norm_num)
  have hδ_le_one : δ ≤ 1 := min_le_right _ _
  have hδ_le_δ₁ : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_δ₂ : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  refine ⟨δ, hδ_pos, hδ_le_one, ?_⟩
  -- Apply path_lift_eqOn_Icc_of_continuousOn.
  -- γ₂ is ContinuousOn (Icc 0 δ), via composition of ContinuousOn sheet.g (sheet.V)
  -- with continuous β∘σ mapping [0, δ] to sheet.V.
  have hβσ_mapsTo : Set.MapsTo (fun t : ℝ => β (Real.smoothTransition t))
      (Icc (0 : ℝ) δ) sheet.V := by
    intro t ht
    apply hδ₁_sub
    exact ⟨ht.1, le_trans ht.2 hδ_le_δ₁⟩
  have hγ₂_contOn : ContinuousOn γ₂ (Icc (0 : ℝ) δ) :=
    hsheet_g_contOn.comp' hβσ_cont.continuousOn hβσ_mapsTo
  have hγ₁_contOn : ContinuousOn γ₁ (Icc (0 : ℝ) δ) := hγ₁_cont.continuousOn
  -- Both paths lift β ∘ σ on [0, δ].
  have hγ₁_lift : ∀ t ∈ Icc (0 : ℝ) δ,
      f.toRiemannSphere (γ₁ t) = β (Real.smoothTransition t) := by
    intro t ht
    -- Use sourceFiberPath_toPath_lifts.
    have h_unit : Real.smoothTransition t ∈ unitInterval :=
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have ht_unit : t ∈ unitInterval := by
      refine ⟨ht.1, ?_⟩
      exact le_trans ht.2 hδ_le_one
    show f.toRiemannSphere
        ((f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend t)
          = β (Real.smoothTransition t)
    rw [Path.extend_extends' _ ⟨t, ht_unit⟩]
    exact f.sourceFiberPath_toPath_lifts hnc hβ_smooth hβ_reg hx ⟨t, ht_unit⟩
  have hγ₂_lift : ∀ t ∈ Icc (0 : ℝ) δ,
      f.toRiemannSphere (γ₂ t) = β (Real.smoothTransition t) := by
    intro t ht
    show f.toRiemannSphere (sheet.g (β (Real.smoothTransition t)))
      = β (Real.smoothTransition t)
    exact sheet.rightInvOn (hβσ_mapsTo ht)
  -- Lift hypothesis for path_lift_eqOn_Icc_of_continuousOn: β∘σ regular on [0, δ].
  have hβσ_reg : ∀ t ∈ Icc (0 : ℝ) δ,
      β (Real.smoothTransition t) ∈ f.regularValueSet := by
    intro t ht
    apply hβ_reg
    refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- Agreement at t = 0.
  have h_start : γ₁ 0 = γ₂ 0 := by
    show (f.sourceFiberPath hnc hβ_smooth hβ_reg hx).toPath.extend 0
      = sheet.g (β (Real.smoothTransition 0))
    rw [Path.extend_zero, Real.smoothTransition.zero]
    rw [show β 0 = f.toRiemannSphere x from hx.symm]
    rw [f.sourceFiberPath_src hnc hβ_smooth hβ_reg hx]
    exact (sheet.leftInvOn hx_in_U).symm
  -- Apply uniqueness.
  have h_eqOn : Set.EqOn γ₁ γ₂ (Icc (0 : ℝ) δ) :=
    f.path_lift_eqOn_Icc_of_continuousOn hβσ_reg hγ₁_contOn hγ₂_contOn
      hγ₁_lift hγ₂_lift (t₀ := 0) ⟨le_refl _, hδ_pos.le⟩ h_start
  intro t ht
  exact h_eqOn ht

end MeromorphicNonzero

end JacobianChallenge

end
