/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.NearbyRegularWitnessUnconditional
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.PreimageEventualContainment
import JacobianChallenge.Manifold.DisjointFibreNbhds
import JacobianChallenge.Manifold.RamificationIndexPositive
import JacobianChallenge.Manifold.PerChartNonConstancyReduction
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Fibre-disjoint chart-radius decomposition at `y₀ : Y` (chip P1.2d-ii / ZZ211)

For a non-constant `C^ω` map `f : X → Y` between compact connected complex
1-manifolds and any `y₀ : Y`, this file packages a fibre-disjoint chart-radius
decomposition at `y₀`:

* For each preimage point `x ∈ (f ⁻¹' {y₀}).toFinset`, an open chart-disk.
  `D_x = (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_x`
  with `ε_x > 0`.
* The chart-disks `(D_x)_x` are pairwise disjoint.
* A common open neighbourhood `V ∋ y₀` such that:
  - `f ⁻¹' V ⊆ ⋃ x ∈ FF, D_x` (preimage containment), and
  - For every `y ∈ V \ {y₀}` and every `x ∈ FF`,
    `(f ⁻¹' {y} ∩ D_x).ncard = manifoldRamificationIndex f x`.
* Consequence: for `y ∈ V \ {y₀}`, `f ⁻¹' {y}` is the disjoint union of the
  `f ⁻¹' {y} ∩ D_x` over `x ∈ FF`, with cardinalities equal to the
  ramification indices.

This is exactly the per-`y₀` data needed by chip ZZ212 (P1.2d-iii) to
construct the per-factor functions of `ChartLocalProductWitnessData`.

The decomposition itself is precisely the construction inlined inside
`nearbyRegularWitnessHypothesis_holds_unconditional`; this file factors it
out into a reusable theorem.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Function
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace Manifold

universe u v

/-- **Fibre-disjoint chart-radius decomposition at `y₀`.**

For non-constant `C^ω` `f : X → Y`, every `y₀ : Y` admits an open
neighbourhood `V ∋ y₀` and, for each `x ∈ (f ⁻¹' {y₀}).toFinset`, a
chart-radius `ε_x > 0` whose chart-disk
`D_x := (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε_x`
satisfies:

* `x ∈ D_x` and `D_x` is open;
* the family `(D_x)_x` is pairwise disjoint;
* `f ⁻¹' V ⊆ ⋃ x ∈ FF, D_x`;
* for every `y ∈ V` with `y ≠ y₀` and every `x ∈ FF`,
  `(f ⁻¹' {y} ∩ D_x).ncard = manifoldRamificationIndex f x`.
-/
open Classical in
theorem fibre_disjoint_chart_radius_decomposition
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (y₀ : Y) :
    ∃ (hF : (f ⁻¹' {y₀}).Finite)
      (ε_fn : ∀ x ∈ hF.toFinset, ℝ)
      (V : Set Y),
      IsOpen V ∧ y₀ ∈ V ∧
      (∀ x (hx : x ∈ hF.toFinset), 0 < ε_fn x hx) ∧
      -- pairwise disjoint chart-disks
      ((hF.toFinset : Set X).PairwiseDisjoint
        (fun x => (chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹'
            Metric.ball ((chartAt ℂ x) x)
              (if h : x ∈ hF.toFinset then ε_fn x h else 0))) ∧
      -- preimage of V is contained in the union of chart-disks
      (f ⁻¹' V ⊆ ⋃ x ∈ hF.toFinset,
        ((chartAt ℂ x).source ∩
          (chartAt ℂ x) ⁻¹'
            Metric.ball ((chartAt ℂ x) x)
              (if h : x ∈ hF.toFinset then ε_fn x h else 0))) ∧
      -- per-fibre count: for y ∈ V \ {y₀}, count near each x equals k_x
      (∀ y ∈ V, y ≠ y₀ → ∀ x (hx : x ∈ hF.toFinset),
        (f ⁻¹' {y} ∩
          ((chartAt ℂ x).source ∩
            (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (ε_fn x hx))).ncard
          = manifoldRamificationIndex f x) := by
  classical
  -- Step 1: fibre F over y₀ is finite.
  have hF_fin : (f ⁻¹' {y₀}).Finite :=
    JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
      f hf hnc y₀
  set F : Set X := f ⁻¹' {y₀} with hF_def
  set FF : Finset X := hF_fin.toFinset with hFF_def
  -- Step 2: t2-separator W on the finite F.
  obtain ⟨W, hW_mem_open, hW_disj⟩ := exists_disjoint_open_nbhds_of_finite hF_fin
  -- Per-chart non-constancy hypothesis (used for ramification positivity).
  have h_perChartNonConst :
      JacobianChallenge.ContMDiff.Owed.degree.PerChartNonConstancyHypothesis X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.perChartNonConstancy_of_clopennessOfLocallyConst
      JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  -- Step 3: per-x existential — chart-radius witness with chart-disk ⊆ W x.
  have h_per_x : ∀ x ∈ FF, ∃ (ε : ℝ) (V : Set Y),
      0 < ε ∧ IsOpen V ∧ f x ∈ V ∧
        ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε) ⊆ W x ∧
        (∀ w ∈ V, w ≠ f x →
          (f ⁻¹' {w} ∩
            ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
            = manifoldRamificationIndex f x) := by
    intro x hxFF
    have hxF : x ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hxFF
    have hxy : f x = y₀ := hxF
    have hpos : 1 ≤ manifoldRamificationIndex f x :=
      manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
        h_perChartNonConst hf hnc hxy
    have hxWx : x ∈ W x := (hW_mem_open x hxF).1
    have hWx_open : IsOpen (W x) := (hW_mem_open x hxF).2
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
    have hxc : x ∈ c.source := mem_chart_source ℂ x
    have h_target_nhds : c.target ∈ 𝓝 (c x) :=
      c.open_target.mem_nhds (c.map_source hxc)
    have h_symm_cx : c.symm (c x) = x := c.left_inv hxc
    have h_symm_cont : ContinuousAt c.symm (c x) := by
      have h_co : ContinuousOn c.symm c.target := c.continuousOn_invFun
      exact h_co.continuousAt h_target_nhds
    have h_pre_nhds : c.symm ⁻¹' (W x) ∈ 𝓝 (c x) := by
      have ht := h_symm_cont.tendsto
      rw [h_symm_cx] at ht
      exact ht (hWx_open.mem_nhds hxWx)
    have h_inter_nhds : c.target ∩ c.symm ⁻¹' (W x) ∈ 𝓝 (c x) :=
      Filter.inter_mem h_target_nhds h_pre_nhds
    obtain ⟨R₀, hR₀_pos, hR₀_sub⟩ := Metric.mem_nhds_iff.mp h_inter_nhds
    obtain ⟨ε, V, hε_pos, hε_le_R₀, hV_open, h_fx_V, h_count⟩ :=
      localKFoldMultiplicityOnManifold_genuine_with_radius hf x hpos hR₀_pos
    have h_Dx_sub_W :
        ((c.source ∩ c ⁻¹' Metric.ball (c x) ε) : Set X) ⊆ W x := by
      intro z hz
      obtain ⟨hz_src, hz_ball⟩ := hz
      have hcz_target_W : c z ∈ c.target ∩ c.symm ⁻¹' W x :=
        hR₀_sub (Metric.ball_subset_ball hε_le_R₀ hz_ball)
      have hcz_pre : c.symm (c z) ∈ W x := hcz_target_W.2
      have hsymm_cz : c.symm (c z) = z := c.left_inv hz_src
      rw [hsymm_cz] at hcz_pre
      exact hcz_pre
    refine ⟨ε, V, hε_pos, hV_open, h_fx_V, ?_, h_count⟩
    exact h_Dx_sub_W
  choose ε_fn V_fn hε_pos_fn hV_open_fn h_fx_V_fn h_Dx_sub_W_fn h_count_fn using h_per_x
  -- D_x : X → Set X using the dependent if-then-else.
  set D_x : X → Set X := fun x' =>
    (chartAt ℂ x').source ∩ (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
      if h : x' ∈ FF then ε_fn x' h else 0) with hD_def
  -- D_x for x' ∈ FF is open.
  have hD_open : ∀ x' ∈ FF, IsOpen (D_x x') := by
    intro x' hx'F
    show IsOpen ((chartAt ℂ x').source ∩
      (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
        if h : x' ∈ FF then ε_fn x' h else 0))
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'F from dif_pos hx'F]
    have hco : ContinuousOn (chartAt ℂ x') (chartAt ℂ x').source :=
      (chartAt ℂ x').continuousOn_toFun
    exact hco.isOpen_inter_preimage (chartAt ℂ x').open_source Metric.isOpen_ball
  -- x' ∈ D_x x'.
  have hxD : ∀ x' ∈ FF, x' ∈ D_x x' := by
    intro x' hx'F
    show x' ∈ (chartAt ℂ x').source ∩
      (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
        if h : x' ∈ FF then ε_fn x' h else 0)
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'F from dif_pos hx'F]
    refine ⟨mem_chart_source ℂ x', ?_⟩
    show (chartAt ℂ x') x' ∈ Metric.ball ((chartAt ℂ x') x') (ε_fn x' hx'F)
    exact Metric.mem_ball_self (hε_pos_fn x' hx'F)
  -- D_x ⊆ W x'.
  have hD_sub_W : ∀ x' ∈ FF, D_x x' ⊆ W x' := by
    intro x' hx'F
    show ((chartAt ℂ x').source ∩
      (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
        if h : x' ∈ FF then ε_fn x' h else 0)) ⊆ W x'
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'F from dif_pos hx'F]
    exact h_Dx_sub_W_fn x' hx'F
  -- Pairwise disjoint as sets indexed by F.
  have hD_pwd_F : F.PairwiseDisjoint D_x := by
    intro a haF b hbF hab
    have haFF : a ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using haF
    have hbFF : b ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using hbF
    have hWab : Disjoint (W a) (W b) := hW_disj haF hbF hab
    exact hWab.mono (hD_sub_W a haFF) (hD_sub_W b hbFF)
  -- Pairwise disjoint as sets indexed by FF (the toFinset, viewed as Set X).
  have hD_pwd : (FF : Set X).PairwiseDisjoint D_x := by
    intro a haFF b hbFF hab
    have haF : a ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using haFF
    have hbF : b ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hbFF
    exact hD_pwd_F haF hbF hab
  -- Step 4: PreimageEventualContainment: open V₀ ∋ y₀ with f⁻¹V₀ ⊆ ⋃ D_x.
  have hf_cont : Continuous f := hf.continuous
  have hD_open_F : ∀ x' ∈ F, IsOpen (D_x x') := by
    intro x' hx'F
    have hx'FF : x' ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'F
    exact hD_open x' hx'FF
  have hxD_F : ∀ x' ∈ F, x' ∈ D_x x' := by
    intro x' hx'F
    have hx'FF : x' ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'F
    exact hxD x' hx'FF
  obtain ⟨V₀, hV₀_open, hyV₀, hV₀_sub⟩ :=
    JacobianChallenge.PreimageEventualContainment.preimage_eventually_in_fibre_neighbourhoods
      hf_cont y₀ hF_fin D_x hD_open_F hxD_F
  -- Step 5: define V_fn' : default-extended V_fn so we can iIntersection.
  set V_fn' : X → Set Y := fun x' =>
    if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y) with hV_fn'_def
  have hV_fn'_open : ∀ x' ∈ FF, IsOpen (V_fn' x') := by
    intro x' hx'FF
    show IsOpen (if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y))
    rw [dif_pos hx'FF]; exact hV_open_fn x' hx'FF
  have hV_fn'_y : ∀ x' ∈ FF, y₀ ∈ V_fn' x' := by
    intro x' hx'FF
    have hx'F : x' ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'FF
    have hxy : f x' = y₀ := hx'F
    show y₀ ∈ (if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y))
    rw [dif_pos hx'FF]
    have := h_fx_V_fn x' hx'FF
    rw [hxy] at this
    exact this
  set V_inter : Set Y := V₀ ∩ (⋂ x' ∈ FF, V_fn' x') with hV_inter_def
  have hV_inter_open : IsOpen V_inter := by
    refine hV₀_open.inter ?_
    refine isOpen_biInter_finset ?_
    intro x' hx'FF
    exact hV_fn'_open x' hx'FF
  have hy_V_inter : y₀ ∈ V_inter := by
    refine ⟨hyV₀, ?_⟩
    rw [Set.mem_iInter₂]
    intro x' hx'FF
    exact hV_fn'_y x' hx'FF
  -- Step 6: build ε_fn_out as the dependent function on FF.
  -- Step 7: package the conclusion.
  refine ⟨hF_fin, fun x hx => ε_fn x hx, V_inter, hV_inter_open, hy_V_inter, ?_, ?_, ?_, ?_⟩
  · -- pos
    intro x hx; exact hε_pos_fn x hx
  · -- pairwise disjoint
    -- Goal: (FF : Set X).PairwiseDisjoint
    --   (fun x => chart-disk with `if h : x ∈ FF then ε_fn x h else 0`)
    -- which equals D_x by definition of D_x.
    show (FF : Set X).PairwiseDisjoint D_x
    exact hD_pwd
  · -- preimage of V_inter ⊆ ⋃ D_x
    intro z hz
    have hz_V₀ : z ∈ f ⁻¹' V₀ := by
      show f z ∈ V₀
      have hz' : f z ∈ V_inter := hz
      exact hz'.1
    have h_un : z ∈ ⋃ x' ∈ FF, D_x x' := hV₀_sub hz_V₀
    -- Goal is the same union written without the `D_x` abbrev.
    show z ∈ ⋃ x' ∈ FF,
      ((chartAt ℂ x').source ∩
        (chartAt ℂ x') ⁻¹'
          Metric.ball ((chartAt ℂ x') x')
            (if h : x' ∈ FF then ε_fn x' h else 0))
    exact h_un
  · -- per-fibre count
    intro y hyV hyne x hxFF
    -- Need: (f⁻¹{y} ∩ chart-disk x with ε = ε_fn x hxFF).ncard = ramif index.
    -- Use h_count_fn: for y ∈ V_fn x hxFF and y ≠ f x, the ncard = ramif.
    have hyV_fn' : y ∈ V_fn' x := by
      have h_iI : y ∈ ⋂ x' ∈ FF, V_fn' x' := hyV.2
      rw [Set.mem_iInter₂] at h_iI
      exact h_iI x hxFF
    have hyV_fn : y ∈ V_fn x hxFF := by
      have heq : V_fn' x = V_fn x hxFF := by
        show (if h : x ∈ FF then V_fn x h else (Set.univ : Set Y)) = V_fn x hxFF
        rw [dif_pos hxFF]
      rw [heq] at hyV_fn'
      exact hyV_fn'
    have hxF : x ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hxFF
    have hxy : f x = y₀ := hxF
    have hyne_fx : y ≠ f x := by rw [hxy]; exact hyne
    exact h_count_fn x hxFF y hyV_fn hyne_fx

end Manifold
end JacobianChallenge

end

end
