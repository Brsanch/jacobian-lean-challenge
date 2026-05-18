/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphism
import JacobianChallenge.Manifold.ChartPullbackLocalInverse
import JacobianChallenge.Manifold.ContMDiffAnalyticBridge
import Mathlib.Topology.Homeomorph.Lemmas

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Discharge: `BijectiveAnalyticIsBiholomorphism X` UNCONDITIONALLY

A globally bijective `ω`-smooth map `f : X → Y` between compact connected
complex 1-manifolds upgrades to a `HolomorphicEquiv X Y`
(= `Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) X Y ω`).

The classical content is the inverse function theorem at every point,
applied to the chart pullback `(chartAt (f x)) ∘ f ∘ (chartAt x).symm`,
whose derivative is non-vanishing because `f` is globally injective
(`ContMDiff.deriv_chart_pullback_ne_zero_of_injective`). The local
analytic inverse from `ChartPullbackLocalInverse.lean` then agrees with
the chart pullback of `f⁻¹` on a chart-coord neighbourhood, giving
analyticity of the chart pullback of `f⁻¹` and hence
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f⁻¹ y` at every `y` via the iff bridge
`contMDiffAt_omega_iff_analyticAt_chart_pullback`.

This closes the four-input chain for item-14 strict closure
(`BijectiveAnalyticToBiholomorphism.lean`):

* `ramificationSumEqualsDegree_statement` — discharged.
* `Surjective_of_NonConstant_Analytic_Manifold` — discharged
  (`SurjectiveOfNonConstantDischarge.lean`).
* `BijectiveAnalyticIsBiholomorphism` — discharged here.
* `RiemannRochGenusZero` — still open.

Three of the four are now closed.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open Set Filter Function

noncomputable section

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Key helper: chart pullback of `e⁻¹` equals the analytic local inverse
near the chart image.**

Given `f : X → Y` bijective + ω-smooth, fix `y : Y`. Let `e := Equiv.ofBijective`,
`x := e.symm y`. The chart pullback of `e.symm` at `(chartAt y) y` agrees
with the local analytic inverse `h` of the chart pullback of `f` at
`(chartAt x) x`, on a neighbourhood. -/
private lemma chartPullback_invFun_eventuallyEq_localInverse
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hbij : Function.Bijective f) (y : Y) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h ((chartAt ℂ y) y) ∧
      ContinuousAt
        ((Equiv.ofBijective f hbij).symm : Y → X) y ∧
      (∀ᶠ w in 𝓝 ((chartAt ℂ y) y),
        ((chartAt ℂ ((Equiv.ofBijective f hbij).symm y)) ∘
          (Equiv.ofBijective f hbij).symm ∘ (chartAt ℂ y).symm) w = h w) := by
  -- Names.
  set e : X ≃ Y := Equiv.ofBijective f hbij with he_def
  set x : X := e.symm y with hx_def
  have hfx : f x = y := e.apply_symm_apply y
  -- Continuity of `e` (from `ContMDiff`) and of `e.symm` (compact + T2).
  have hf_cont : Continuous f := hf.continuous
  let e_homeo : X ≃ₜ Y := Continuous.homeoOfEquivCompactToT2 (X := X) (Y := Y)
    (f := e) hf_cont
  have h_symm_cont : Continuous e.symm := e_homeo.continuous_invFun
  have h_symm_contAt : ContinuousAt (e.symm : Y → X) y := h_symm_cont.continuousAt
  -- The local analytic inverse from `ChartPullbackLocalInverse`.
  obtain ⟨h, h_an_at_chart_fx, h_left, _h_right⟩ :=
    Manifold.ContMDiff.chartPullback_localInverse_of_injective hf
      hbij.injective x
  -- `h` is `AnalyticAt ℂ h ((chartAt ℂ (f x)) (f x))`. Use `f x = y`.
  rw [hfx] at h_an_at_chart_fx h_left
  refine ⟨h, h_an_at_chart_fx, h_symm_contAt, ?_⟩
  -- Setup the chart pullback of `f`: `g := (chartAt y) ∘ f ∘ (chartAt x).symm`.
  set g : ℂ → ℂ := (chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm with hg_def
  -- h_left now reads: `∀ᶠ z in 𝓝 ((chartAt x) x), h (g z) = z`.
  -- Note: `g` is `(chartAt (f x)) ∘ f ∘ (chartAt x).symm`. With `f x = y`,
  -- this matches `hg_def` since `chartAt (f x) = chartAt y` (which is
  -- definitionally true after substituting `f x = y`).
  -- The chart pullback of `e.symm`: `K := (chartAt x) ∘ e.symm ∘ (chartAt y).symm`.
  set K : ℂ → ℂ := (chartAt ℂ x) ∘ e.symm ∘ (chartAt ℂ y).symm with hK_def
  -- Strategy: show
  -- (1) K is continuous at `(chartAt y) y` with K ((chartAt y) y) = (chartAt x) x.
  -- (2) g ∘ K = id near `(chartAt y) y`.
  -- Then `h w = h (g (K w)) = K w` by eventually-left-inverse applied at K w.
  -- Step 1: K is continuous + K maps (chartAt y) y to (chartAt x) x.
  have h_chart_y_symm : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
    (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hK_at : K ((chartAt ℂ y) y) = (chartAt ℂ x) x := by
    show (chartAt ℂ x) (e.symm ((chartAt ℂ y).symm ((chartAt ℂ y) y))) = (chartAt ℂ x) x
    rw [h_chart_y_symm]
  -- Continuity of K at (chartAt y) y.
  have hChart_y_symm_contAt : ContinuousAt (chartAt ℂ y).symm ((chartAt ℂ y) y) :=
    (chartAt ℂ y).continuousAt_symm
      ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
  have hChart_x_contAt : ContinuousAt (chartAt ℂ x) x :=
    (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  -- Compose: (chartAt x) ∘ e.symm ∘ (chartAt y).symm is continuous at (chartAt y) y.
  -- Use ContinuousAt.comp_of_eq for each composition step to handle the
  -- point-substitution explicitly.
  have h1 : ContinuousAt (e.symm ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) :=
    h_symm_contAt.comp_of_eq hChart_y_symm_contAt h_chart_y_symm
  have hcomp_val : (e.symm ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = x := by
    show e.symm ((chartAt ℂ y).symm ((chartAt ℂ y) y)) = x
    rw [h_chart_y_symm]
  have hK_contAt : ContinuousAt K ((chartAt ℂ y) y) :=
    hChart_x_contAt.comp_of_eq h1 hcomp_val
  -- Step 2: g ∘ K = id near (chartAt y) y.
  -- Specifically: on a nbhd of (chartAt y) y, ALL these hold:
  --   (a) (chartAt y).symm w ∈ chartSource y (continuity of (chartAt y).symm into chartSource y).
  --   (b) e.symm ((chartAt y).symm w) ∈ chartSource x (continuity + open chart source).
  --   (c) w ∈ chartTarget y (chartAt y is at-y; mem_chart_source etc.).
  -- These together give g (K w) = w.
  -- Subgoal: the set where these hold is a nbhd of (chartAt y) y.
  have h_chart_y_target_nhds : (chartAt ℂ y).target ∈ 𝓝 ((chartAt ℂ y) y) :=
    (chartAt ℂ y).open_target.mem_nhds ((chartAt ℂ y).map_source (mem_chart_source ℂ y))
  -- pre-image of chartSource y under (chartAt y).symm: this is chartTarget y restricted.
  -- For w ∈ chartTarget y, (chartAt y).symm w ∈ chartSource y by chart.map_target.
  -- pre-image of chartSource x under e.symm: open by continuity.
  have h_pre_x : IsOpen (e.symm ⁻¹' (chartAt ℂ x).source) :=
    (chartAt ℂ x).open_source.preimage h_symm_cont
  have hy_in_pre_x : y ∈ e.symm ⁻¹' (chartAt ℂ x).source := by
    show e.symm y ∈ (chartAt ℂ x).source
    rw [← hx_def]
    exact mem_chart_source ℂ x
  have h_pre_x_nhds : e.symm ⁻¹' (chartAt ℂ x).source ∈ 𝓝 y :=
    h_pre_x.mem_nhds hy_in_pre_x
  -- Pull back through (chartAt y).symm: pre-image is a nbhd of (chartAt y) y in chartTarget.
  have h_chart_y_symm_pre_nhds :
      (chartAt ℂ y).symm ⁻¹' (e.symm ⁻¹' (chartAt ℂ x).source) ∈ 𝓝 ((chartAt ℂ y) y) := by
    apply hChart_y_symm_contAt.preimage_mem_nhds
    rw [h_chart_y_symm]
    exact h_pre_x_nhds
  -- Combine with chartTarget membership.
  have h_combined_nhds :
      (chartAt ℂ y).target ∩ ((chartAt ℂ y).symm ⁻¹' (e.symm ⁻¹' (chartAt ℂ x).source))
        ∈ 𝓝 ((chartAt ℂ y) y) :=
    inter_mem h_chart_y_target_nhds h_chart_y_symm_pre_nhds
  -- On this combined nbhd, g (K w) = w.
  have h_g_K_eq_id :
      ∀ᶠ w in 𝓝 ((chartAt ℂ y) y), g (K w) = w := by
    filter_upwards [h_combined_nhds] with w hw
    obtain ⟨hw_target, hw_pre⟩ := hw
    -- (chartAt y).symm w ∈ chartSource y because w ∈ chartTarget y.
    have h_symm_w_src : (chartAt ℂ y).symm w ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target hw_target
    -- (chartAt y) ((chartAt y).symm w) = w by chart.right_inv.
    have h_chart_right : (chartAt ℂ y) ((chartAt ℂ y).symm w) = w :=
      (chartAt ℂ y).right_inv hw_target
    -- e.symm ((chartAt y).symm w) ∈ chartSource x by hw_pre.
    have h_ex_src : e.symm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source := hw_pre
    -- (chartAt x).symm ((chartAt x) (e.symm ((chartAt y).symm w))) = e.symm ((chartAt y).symm w)
    have h_chart_x_left :
        (chartAt ℂ x).symm ((chartAt ℂ x) (e.symm ((chartAt ℂ y).symm w)))
          = e.symm ((chartAt ℂ y).symm w) :=
      (chartAt ℂ x).left_inv h_ex_src
    -- Now compute.
    show ((chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm) (K w) = w
    show (chartAt ℂ y) (f ((chartAt ℂ x).symm
            ((chartAt ℂ x) (e.symm ((chartAt ℂ y).symm w))))) = w
    rw [h_chart_x_left]
    show (chartAt ℂ y) (f (e.symm ((chartAt ℂ y).symm w))) = w
    have h_f_e_symm : f (e.symm ((chartAt ℂ y).symm w)) = (chartAt ℂ y).symm w :=
      e.apply_symm_apply _
    rw [h_f_e_symm, h_chart_right]
  -- Final: use eventually-left-inverse on a nbhd where K w is near (chartAt x) x.
  -- Continuity of K + K((chartAt y) y) = (chartAt x) x means: for w near (chartAt y) y,
  -- K w is near (chartAt x) x. So the eventually-left-inverse h (g z) = z at
  -- z := K w gives h (g (K w)) = K w. Combined with g (K w) = w: h w = K w.
  have h_K_pre_left : ∀ᶠ w in 𝓝 ((chartAt ℂ y) y), h (g (K w)) = K w := by
    -- Need: {z | h (g z) = z} ∈ 𝓝 (K ((chartAt y) y)) = 𝓝 ((chartAt x) x).
    have h_target_nhds : {z | h (g z) = z} ∈ 𝓝 (K ((chartAt ℂ y) y)) := by
      rw [hK_at]; exact h_left
    exact hK_contAt.preimage_mem_nhds h_target_nhds
  filter_upwards [h_g_K_eq_id, h_K_pre_left] with w hgK hKpre
  -- hgK : g (K w) = w
  -- hKpre : h (g (K w)) = K w
  rw [hgK] at hKpre
  -- hKpre : h w = K w
  exact hKpre.symm

/-- **Discharge of `BijectiveAnalyticIsBiholomorphism X`.**
A globally bijective `ω`-smooth map `f : X → Y` between compact connected
complex 1-manifolds upgrades to a `HolomorphicEquiv X Y`. -/
theorem bijectiveAnalyticIsBiholomorphism_holds
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    BijectiveAnalyticIsBiholomorphism X := by
  intro Y _ _ _ _ _ _ f hf hbij
  set e : X ≃ Y := Equiv.ofBijective f hbij with he_def
  -- ContMDiff of e.symm at every y.
  have h_inv_smooth : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω e.symm := by
    intro y
    obtain ⟨h, h_an, h_cont, h_eq⟩ :=
      chartPullback_invFun_eventuallyEq_localInverse hf hbij y
    -- Chart pullback of e.symm at y equals h on a nbhd of (chartAt y) y.
    -- So chart pullback is AnalyticAt at (chartAt y) y.
    have h_eq_sym :
        h =ᶠ[𝓝 ((chartAt ℂ y) y)]
          ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm) := by
      filter_upwards [h_eq] with w hw
      exact hw.symm
    have h_chart_an :
        AnalyticAt ℂ
          ((chartAt ℂ (e.symm y)) ∘ e.symm ∘ (chartAt ℂ y).symm)
          ((chartAt ℂ y) y) :=
      h_an.congr h_eq_sym
    -- Apply the iff bridge: continuous + chart-pullback analytic → ContMDiffAt ω.
    exact ContMDiff.Owed.degree.contMDiffAt_omega_of_analyticAt_chart_pullback
      h_cont h_chart_an
  -- Build the Diffeomorph.
  refine ⟨{
    toEquiv := e
    contMDiff_toFun := hf
    contMDiff_invFun := h_inv_smooth }⟩

end JacobianChallenge

end
