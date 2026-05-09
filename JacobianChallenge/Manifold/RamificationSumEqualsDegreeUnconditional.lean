/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationSumComposer
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional
import JacobianChallenge.Manifold.HurwitzWellDefinedUnconditionalTopo
import JacobianChallenge.Manifold.HLcUnconditional
import JacobianChallenge.Manifold.LocalSheetDataFromContMDiff
import JacobianChallenge.Manifold.CriticalValuesFiniteGeneral
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.ChartPullbackNotEventuallyConstDischarge
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge
import JacobianChallenge.Manifold.MeromorphicAt

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Reduction of `ramificationSumEqualsDegree_statement` after RegFix (RH-Final-v2)

This file ships the structural reduction post-RegFix:

* The `ClassicalChoiceRegularHypothesis` slot of the composer is gone — RegFix
  made the choice be over `RegularValueWitnessReg f` directly, so the
  hypothesis was discharged in `RamificationSumComposer.lean`.

* The `h_wd_reg` slot (constancy of `RegularValueWitnessReg.card` across the
  chosen witnesses) is **discharged unconditionally** here, by composing:

  - `criticalValues_finite_general` (CV-Gen): finiteness of the critical-value
    set for any non-constant analytic `f : X → Y`;
  - `LocalSheetData.ofContMDiffMfderivNeZero` (ZZ169): a `LocalSheetData` from
    `ContMDiffAt … ω` plus chart-pullback-derivative-nonzero;
  - `notInjOn_iff_deriv_zero_of_analytic_of_order` (ZZ99): the planar bridge
    "locally injective ⇒ chart-pullback derivative nonzero";
  - `h_lc_holds_for_subset_of_localSheets_supplier` (ZZ158): a per-`y`
    `LocalSheetData` supplier discharges the locally-constant fibre-ncard on
    the regular subset;
  - `fibre_card_well_defined_at_regular_holds_of_h_pkg` (ZZ176): packages all
    of the above with the unconditional path-connectedness of finite-complement
    subsets to deliver the well-definedness conclusion.

* The single residual is `NearbyRegularWitnessHypothesis X Y`: existence, for
  every non-constant `f` and every `y : Y`, of a *nearby* regular value `w`
  whose fibre cardinality equals `∑_{x ∈ fibre y} k_x`. This is the analytic
  Hurwitz total-weight identity (planar k-fold count + disjoint-disks
  patching) — it is named here as `h_near_y` and consumed as the only
  remaining input.

## What this file ships

* `wd_reg_holds_unconditional` — the well-definedness of `card` on
  `RegularValueWitnessReg f`, discharged unconditionally.

* `ramificationSumEqualsDegree_holds_of_nearby_regular_witness_only` — the
  named obligation, reduced to a single `h_near_y` hypothesis (post-RegFix
  the only remaining input).

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-! ## Auxiliary: chart-pullback derivative nonzero from local injectivity

This is the public re-derivation of the (private) helper
`deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood` in
`RegularValueExistsRegUnconditional.lean`. Same proof, exported so the
`LocalSheetData` supplier here can call it directly. -/

private lemma deriv_chart_pullback_ne_zero_of_inj
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) (x : X)
    (h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U) :
    deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0 := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
  have hFA_at_x : AnalyticAt ℂ F (c x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  have hClop :
      JacobianChallenge.ContMDiff.Owed.degree.ClopennessOfLocallyConstHypothesis
        X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      JacobianChallenge.ContMDiff.Owed.degree.ChartPullbackNotEventuallyConstHypothesis
        X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x) :=
    hChartNEC f hf hnc (f x) x rfl
  have hFcx : F (c x) = d (f x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f ∘ c.symm) (c x) = d (f x)
    simp [Function.comp, h_inv]
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)
      have : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = F z from rfl,
          this, hFcx])
  have h_inj_F : ∃ U' ∈ 𝓝 (c x), Set.InjOn F U' := by
    obtain ⟨U, hU_nhds, hU_inj⟩ := h_inj
    set U₁ : Set X := U ∩ c.source ∩ f ⁻¹' d.source with hU₁_def
    have hf_cont : Continuous f := hf.continuous
    have hU₁_nhds : U₁ ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem hU_nhds (c.open_source.mem_nhds hxc))
        (hf_cont.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hfx_d))
    have hU₁_subc : U₁ ⊆ c.source := fun _ hy => hy.1.2
    obtain ⟨U₁_open, hU₁_open_open, hU₁_open_sub, hx_U₁_open⟩ :
        ∃ U_o, IsOpen U_o ∧ U_o ⊆ U₁ ∧ x ∈ U_o := by
      obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
      exact ⟨W, hW_open, hW_sub, hxW⟩
    have hU₁_open_subc : U₁_open ⊆ c.source := hU₁_open_sub.trans hU₁_subc
    set U' : Set ℂ := c '' U₁_open with hU'_def
    have hU'_open : IsOpen U' :=
      c.isOpen_image_of_subset_source hU₁_open_open hU₁_open_subc
    have hcx_in_U' : c x ∈ U' := ⟨x, hx_U₁_open, rfl⟩
    have hU'_nhds : U' ∈ 𝓝 (c x) := hU'_open.mem_nhds hcx_in_U'
    refine ⟨U', hU'_nhds, ?_⟩
    rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF_eq
    have hy₁_subc : y₁ ∈ c.source := hU₁_open_subc hy₁_U
    have hy₂_subc : y₂ ∈ c.source := hU₁_open_subc hy₂_U
    have hy₁_U₁ : y₁ ∈ U₁ := hU₁_open_sub hy₁_U
    have hy₂_U₁ : y₂ ∈ U₁ := hU₁_open_sub hy₂_U
    have hy₁_U_outer : y₁ ∈ U := hy₁_U₁.1.1
    have hy₂_U_outer : y₂ ∈ U := hy₂_U₁.1.1
    have hy₁_fd : f y₁ ∈ d.source := hy₁_U₁.2
    have hy₂_fd : f y₂ ∈ d.source := hy₂_U₁.2
    have h_inv_y₁ : c.symm (c y₁) = y₁ := c.left_inv hy₁_subc
    have h_inv_y₂ : c.symm (c y₂) = y₂ := c.left_inv hy₂_subc
    have hF_at_y₁ : F (c y₁) = d (f y₁) := by
      show (d ∘ f ∘ c.symm) (c y₁) = d (f y₁)
      simp [Function.comp, h_inv_y₁]
    have hF_at_y₂ : F (c y₂) = d (f y₂) := by
      show (d ∘ f ∘ c.symm) (c y₂) = d (f y₂)
      simp [Function.comp, h_inv_y₂]
    rw [← hy₁_eq, ← hy₂_eq] at hF_eq
    rw [hF_at_y₁, hF_at_y₂] at hF_eq
    have h_inj_d : Set.InjOn d d.source := d.injOn
    have hf_eq : f y₁ = f y₂ :=
      h_inj_d hy₁_fd hy₂_fd hF_eq
    have hy_eq : y₁ = y₂ := hU_inj hy₁_U_outer hy₂_U_outer hf_eq
    rw [← hy₁_eq, ← hy₂_eq, hy_eq]
  have hFA_sub : AnalyticAt ℂ (fun z => F z - F (c x)) (c x) :=
    hFA_at_x.sub analyticAt_const
  have h_ord_ne_top :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ ⊤ := by
    intro h_top
    apply hFne
    have h := analyticOrderAt_eq_top.mp h_top
    exact h.mono (fun z hz => sub_eq_zero.mp hz)
  have hF_self : (fun z => F z - F (c x)) (c x) = 0 := by simp
  have h_ord_ne_zero :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ 0 := by
    intro h_zero
    have hne := (hFA_sub.analyticOrderAt_eq_zero).mp h_zero
    exact hne hF_self
  set ord : ℕ∞ := analyticOrderAt (fun z => F z - F (c x)) (c x) with hord_def
  obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, ord = (k : ℕ∞) := by
    cases hord_eq : ord with
    | top => exact absurd hord_eq h_ord_ne_top
    | coe n => exact ⟨n, by simp [hord_eq]⟩
  have hk_ge_one : 1 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k
    apply h_ord_ne_zero
    exact hk_eq
  have h_planar :
      (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) ↔ deriv F (c x) = 0 :=
    JacobianChallenge.Manifold.notInjOn_iff_deriv_zero_of_analytic_of_order
      hFA_at_x hk_ge_one hk_eq
  have h_neg_iff : ¬ (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) := by
    intro h_neg
    exact h_neg h_inj_F
  by_contra h_d_zero
  exact h_neg_iff (h_planar.mpr h_d_zero)

/-! ## Locally-injective preimages off the critical-value set

For `y ∉ criticalValuesGeneral f`, every preimage `x` lies outside
`criticalSetGeneral f`, so `f` is locally injective at `x`. -/

private lemma preimages_locally_injective_of_notMem_cv
    {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y]
    {f : X → Y} {y : Y}
    (hy : y ∉ JacobianChallenge.Manifold.criticalValuesGeneral f) :
    ∀ x ∈ f ⁻¹' {y}, ∃ U ∈ 𝓝 x, Set.InjOn f U := by
  intro x hx
  have hfx_eq : f x = y := hx
  have hx_not_crit : x ∉ JacobianChallenge.Manifold.criticalSetGeneral f := by
    intro hx_crit
    apply hy
    exact ⟨x, hx_crit, hfx_eq⟩
  have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
    by_contra h
    apply hx_not_crit
    show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
    exact h
  exact h_inj

/-! ## `LocalSheetData` supplier off the critical-value set

The structural meat: at every `y ∉ criticalValuesGeneral f` and every preimage
`x`, we can build a `LocalSheetData f y x` from the chart-pullback derivative
nonzero certificate (which holds because `f` is locally injective at `x`). -/

private noncomputable def localSheetData_off_criticalValuesGeneral
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f) :
    ∀ y ∈ ((JacobianChallenge.Manifold.criticalValuesGeneral f)ᶜ : Set Y),
      ∀ x ∈ f ⁻¹' {y}, JacobianChallenge.LocalSheetData f y x := by
  intro y hy x hx
  -- y ∉ criticalValuesGeneral f, so f is locally injective at x.
  have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U :=
    preimages_locally_injective_of_notMem_cv hy x hx
  -- Chart-pullback derivative nonzero.
  have hfx_eq : f x = y := hx
  have h_deriv_at_fx :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    deriv_chart_pullback_ne_zero_of_inj hf hnc x h_inj
  -- Move from `f x` to `y` in the goal.
  have h_deriv :
      deriv ((chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 := by
    rw [← hfx_eq]; exact h_deriv_at_fx
  -- ContMDiffAt at x.
  have hf_at : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f x := hf.contMDiffAt
  -- Apply the LocalSheetData builder.
  exact JacobianChallenge.LocalSheetData.ofContMDiffMfderivNeZero
    hf_at hfx_eq h_deriv

/-! ## Regular witnesses live off the critical-value set

Every `RegularValueWitnessReg f` has its value off `criticalValuesGeneral f`.
The `is_regular` field gives chart-pullback-deriv ≠ 0 at every preimage,
which (via ZZ99 contrapositive) forces local injectivity at every preimage,
which forces no preimage to be in `criticalSetGeneral f`. -/

private lemma regularWitness_value_notMem_criticalValuesGeneral
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (w : RegularValueWitnessReg f) :
    w.toWitness.value ∉ JacobianChallenge.Manifold.criticalValuesGeneral f := by
  classical
  intro h_in
  -- h_in : ∃ x ∈ criticalSetGeneral f, f x = w.toWitness.value
  obtain ⟨x, hx_crit, hfx⟩ := h_in
  -- hx_crit : x ∈ criticalSetGeneral f, i.e. ¬ ∃ U ∈ 𝓝 x, InjOn f U.
  -- The is_regular field gives chart-pullback derivative nonzero at this x.
  have hx_in_pre : x ∈ f ⁻¹' {w.toWitness.value} := by
    show f x = w.toWitness.value
    exact hfx
  have h_deriv :
      deriv ((chartAt ℂ w.toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    w.is_regular x hx_in_pre
  -- hfx : f x = w.toWitness.value, rewrite to get deriv at f x.
  have h_deriv_fx :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 := by
    rw [hfx]; exact h_deriv
  -- Mirror the argument structure of `deriv_chart_pullback_ne_zero_of_inj`
  -- backwards: derive ¬ deriv = 0 ⇒ local injectivity via ZZ99.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hFA_at_x : AnalyticAt ℂ F (c x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  -- ZZ99 needs an order; derive it from non-eventual-constancy.
  have hClop :
      JacobianChallenge.ContMDiff.Owed.degree.ClopennessOfLocallyConstHypothesis
        X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      JacobianChallenge.ContMDiff.Owed.degree.ChartPullbackNotEventuallyConstHypothesis
        X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x) :=
    hChartNEC f hf hnc (f x) x rfl
  have hFcx : F (c x) = d (f x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f ∘ c.symm) (c x) = d (f x)
    simp [Function.comp, h_inv]
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)
      have : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = F z from rfl,
          this, hFcx])
  have hFA_sub : AnalyticAt ℂ (fun z => F z - F (c x)) (c x) :=
    hFA_at_x.sub analyticAt_const
  have h_ord_ne_top :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ ⊤ := by
    intro h_top
    apply hFne
    have h := analyticOrderAt_eq_top.mp h_top
    exact h.mono (fun z hz => sub_eq_zero.mp hz)
  have hF_self : (fun z => F z - F (c x)) (c x) = 0 := by simp
  have h_ord_ne_zero :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ 0 := by
    intro h_zero
    have hne := (hFA_sub.analyticOrderAt_eq_zero).mp h_zero
    exact hne hF_self
  set ord : ℕ∞ := analyticOrderAt (fun z => F z - F (c x)) (c x) with hord_def
  obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, ord = (k : ℕ∞) := by
    cases hord_eq : ord with
    | top => exact absurd hord_eq h_ord_ne_top
    | coe n => exact ⟨n, by simp [hord_eq]⟩
  have hk_ge_one : 1 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k
    apply h_ord_ne_zero
    exact hk_eq
  -- ZZ99 forward: ¬ ∃ U ∈ 𝓝 (c x), InjOn F U ↔ deriv F (c x) = 0.
  have h_planar :
      (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) ↔ deriv F (c x) = 0 :=
    JacobianChallenge.Manifold.notInjOn_iff_deriv_zero_of_analytic_of_order
      hFA_at_x hk_ge_one hk_eq
  -- We have `deriv F (c x) ≠ 0` (h_deriv_fx). So `∃ U ∈ 𝓝 (c x), InjOn F U`.
  have h_inj_F : ∃ U ∈ 𝓝 (c x), Set.InjOn F U := by
    by_contra h_neg
    have h_dz : deriv F (c x) = 0 := h_planar.mp h_neg
    exact h_deriv_fx h_dz
  -- Now lift local injectivity of F at c x back to local injectivity of f at x.
  have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
  have hf_cont : Continuous f := hf.continuous
  have h_inj_f : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
    obtain ⟨U', hU'_nhds, hU'_inj⟩ := h_inj_F
    -- Pull back to 𝓝 x via continuity of c.
    have hc_cont_at : ContinuousAt (c : X → ℂ) x :=
      (c.continuousOn.continuousAt (c.open_source.mem_nhds hxc))
    have hU_pre_nhds : c ⁻¹' U' ∈ 𝓝 x := hc_cont_at.preimage_mem_nhds hU'_nhds
    have hsrc_nhds : c.source ∈ 𝓝 x := c.open_source.mem_nhds hxc
    have hd_pre_nhds : f ⁻¹' d.source ∈ 𝓝 x :=
      hf_cont.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hfx_d)
    set V : Set X := c ⁻¹' U' ∩ c.source ∩ f ⁻¹' d.source with hV_def
    have hV_nhds : V ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem hU_pre_nhds hsrc_nhds) hd_pre_nhds
    refine ⟨V, hV_nhds, ?_⟩
    intro a ha b hb hab_f
    have ha_src : a ∈ c.source := ha.1.2
    have hb_src : b ∈ c.source := hb.1.2
    have ha_U' : c a ∈ U' := ha.1.1
    have hb_U' : c b ∈ U' := hb.1.1
    have ha_fd : f a ∈ d.source := ha.2
    have hb_fd : f b ∈ d.source := hb.2
    -- F (c a) = d (f a), F (c b) = d (f b).
    have h_inv_a : c.symm (c a) = a := c.left_inv ha_src
    have h_inv_b : c.symm (c b) = b := c.left_inv hb_src
    have hF_at_a : F (c a) = d (f a) := by
      show (d ∘ f ∘ c.symm) (c a) = d (f a)
      simp [Function.comp, h_inv_a]
    have hF_at_b : F (c b) = d (f b) := by
      show (d ∘ f ∘ c.symm) (c b) = d (f b)
      simp [Function.comp, h_inv_b]
    -- f a = f b ⇒ F (c a) = F (c b).
    have hF_eq : F (c a) = F (c b) := by
      rw [hF_at_a, hF_at_b, hab_f]
    -- F injective on U' ⇒ c a = c b.
    have hca_cb : c a = c b := hU'_inj ha_U' hb_U' hF_eq
    -- c injective on c.source ⇒ a = b.
    exact c.injOn ha_src hb_src hca_cb
  -- Combined: we have local injectivity of f at x — but x ∈ criticalSetGeneral f.
  exact hx_crit h_inj_f

/-! ## Headline: unconditional discharge of `h_wd_reg`

Compose the supplier with `h_lc_holds_for_subset_of_localSheets_supplier` and
then `fibre_card_well_defined_at_regular_holds_of_h_pkg`. -/

/-- **Unconditional discharge of regular-witness card well-definedness.**
For every non-constant analytic `f : X → Y` between compact connected complex
1-manifolds, `RegularValueWitnessReg.card` is constant across regular witnesses.

The proof composes:
* `criticalValues_finite_general` (CV-Gen) for finiteness of the critical-value
  set;
* `LocalSheetData.ofContMDiffMfderivNeZero` (ZZ169) + the deriv-nonzero
  certificate from local injectivity (ZZ99 contrapositive) to supply
  `LocalSheetData` everywhere off the critical-value set;
* `h_lc_holds_for_subset_of_localSheets_supplier` (ZZ158) for local-constancy
  of fibre ncard on the regular subset;
* `fibre_card_well_defined_at_regular_holds_of_h_pkg` (ZZ176) for the
  topological closing argument. -/
theorem wd_reg_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y] :
    ∀ (f : X → Y), ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f →
      ¬ JacobianChallenge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card := by
  apply fibre_card_well_defined_at_regular_holds_of_h_pkg
  intro f hf hnc
  refine ⟨JacobianChallenge.Manifold.criticalValuesGeneral f, ?_, ?_, ?_⟩
  · exact JacobianChallenge.Manifold.criticalValues_finite_general f hf hnc
  · -- Every regular witness's value is off the critical-value set.
    intro w
    exact regularWitness_value_notMem_criticalValuesGeneral hf hnc w
  · -- IsLocallyConstant: via h_lc_holds_for_subset_of_localSheets_supplier.
    apply JacobianChallenge.h_lc_holds_for_subset_of_localSheets_supplier
      hf.continuous
      (C := JacobianChallenge.Manifold.criticalValuesGeneral f)
    · -- Fibres on the complement are finite (ZZ48 — even stronger; on all of Y).
      intro y _hy
      exact fibres_finite_statement_holds_unconditional f hf hnc y
    · -- LocalSheetData on the complement.
      exact localSheetData_off_criticalValuesGeneral f hf hnc

/-! ## Headline reduction: the named obligation modulo `NearbyRegularWitnessHypothesis`

Post-RegFix the only remaining input is `h_near_y` (the analytic Hurwitz
total-weight identity packaged as nearby-regular-witness existence). -/

/-- **Reduction of `ramificationSumEqualsDegree_statement` to `NearbyRegularWitnessHypothesis` (RH-Final-v2).**

Post-RegFix the composer's `h_choice_reg` hypothesis was discharged inside
`RamificationSumComposer.lean`. This file additionally discharges `h_wd_reg`
unconditionally via `wd_reg_holds_unconditional`. The only remaining input
is `h_near_y` — the analytic content packaged as
`NearbyRegularWitnessHypothesis X Y`. -/
theorem ramificationSumEqualsDegree_holds_of_nearby_regular_witness_only
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (h_near_y : NearbyRegularWitnessHypothesis X Y) :
    JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y :=
  ramificationSumEqualsDegree_holds_of_nearby_regular_witness
    h_near_y wd_reg_holds_unconditional

end Owed.degree
end ContMDiff
end JacobianChallenge

end

end
