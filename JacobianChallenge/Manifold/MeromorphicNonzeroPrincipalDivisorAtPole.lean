/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroPrincipalDivisorAtZero
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Step 7d-c — order = -1 at a simple pole

Skeleton (compiles): the chart-pullback `f.toFun ∘ chart.symm` is
`MeromorphicOn` the chart's target via chart-independence
(`MMeromorphicAt.iff_of_isManifold`). -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- `f.toFun ∘ (chartAt ℂ z).symm` is MeromorphicOn the chart's target. -/
lemma toFun_chartPullback_meromorphicOn_chartTarget
    (f : MeromorphicNonzero X) (z : X) :
    MeromorphicOn (f.toFun ∘ (chartAt ℂ z).symm) (chartAt ℂ z).target := by
  intro y hy
  set x := (chartAt ℂ z).symm y with hx_def
  have hx_source : x ∈ (chartAt ℂ z).source := (chartAt ℂ z).map_target hy
  have h_chart_x : (chartAt ℂ z) x = y := (chartAt ℂ z).right_inv hy
  have h_mmero : MMeromorphicAt (𝓘(ℂ, ℂ)) f.toFun x := f.meromorphic x trivial
  have h_in_atlas : (chartAt ℂ z) ∈ atlas ℂ X := chart_mem_atlas ℂ z
  have h_iff : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x ↔
      MeromorphicAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) x) :=
    MMeromorphicAt.iff_of_isManifold h_in_atlas hx_source
  have h_mer : MeromorphicAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) x) :=
    h_iff.mp h_mmero
  rw [h_chart_x] at h_mer
  exact h_mer

/-- Eventually-analytic on the punctured nbhd: poles are isolated. -/
lemma toFun_chartPullback_eventually_analytic
    (f : MeromorphicNonzero X) (z : X) :
    ∀ᶠ y in 𝓝[≠] ((chartAt ℂ z) z),
      AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ z).symm) y := by
  have h_mer_on : MeromorphicOn (f.toFun ∘ (chartAt ℂ z).symm) (chartAt ℂ z).target :=
    f.toFun_chartPullback_meromorphicOn_chartTarget z
  have h_chart_z_in : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := mem_chart_target ℂ z
  have h_event_on_target_diff :=
    h_mer_on.eventually_analyticAt h_chart_z_in
  -- 𝓝[target \ {chart z}] = 𝓝[≠] when target ∈ 𝓝 (chart z).
  have h_target_nbhd : (chartAt ℂ z).target ∈ 𝓝 ((chartAt ℂ z) z) :=
    chart_target_mem_nhds ℂ z
  -- Use that target ∈ 𝓝[≠] (chart z) (since target ∈ 𝓝).
  have h_target_in_punc : (chartAt ℂ z).target ∈ 𝓝[≠] ((chartAt ℂ z) z) :=
    mem_nhdsWithin_of_mem_nhds h_target_nbhd
  -- Rewrite the filter equality.
  have h_diff_eq : (chartAt ℂ z).target \ {(chartAt ℂ z) z}
      = (chartAt ℂ z).target ∩ {(chartAt ℂ z) z}ᶜ := by
    ext; simp [Set.mem_diff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_inter_iff]
  rw [h_diff_eq, nhdsWithin_inter_of_mem h_target_in_punc] at h_event_on_target_diff
  exact h_event_on_target_diff

/-- `f.chartPullback z =ᶠ[𝓝[≠] chart z] (f.toFun ∘ chart.symm)⁻¹` at a pole. -/
lemma chartPullback_eventuallyEq_inv_toFun_at_pole
    (f : MeromorphicNonzero X) {z : X}
    (h_toRS_inf : f.toRiemannSphere z = (OnePoint.infty : RiemannSphere)) :
    f.chartPullback z =ᶠ[𝓝[≠] ((chartAt ℂ z) z)]
      (f.toFun ∘ (chartAt ℂ z).symm)⁻¹ := by
  have h_chart_eq : (chartAt ℂ (f.toRiemannSphere z)
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartS := by
    rw [h_toRS_inf]; rfl
  -- Eventually analytic on 𝓝[≠] (chart z).
  have h_event_analytic := f.toFun_chartPullback_eventually_analytic z
  -- Eventually in chart.target.
  have h_target_nbhd : (chartAt ℂ z).target ∈ 𝓝 ((chartAt ℂ z) z) :=
    chart_target_mem_nhds ℂ z
  have h_target_event_punc : ∀ᶠ y in 𝓝[≠] ((chartAt ℂ z) z),
      y ∈ (chartAt ℂ z).target := by
    rw [Filter.eventually_iff_exists_mem]
    exact ⟨(chartAt ℂ z).target, mem_nhdsWithin_of_mem_nhds h_target_nbhd, fun _ h => h⟩
  -- Combine: ∀ᶠ y, AnalyticAt y ∧ y ∈ target.
  filter_upwards [h_event_analytic, h_target_event_punc] with y hy_an hy_target
  -- Now: at y analytic + in target, the equality holds.
  set x := (chartAt ℂ z).symm y with hx_def
  have hx_source : x ∈ (chartAt ℂ z).source := (chartAt ℂ z).map_target hy_target
  have h_chart_x : (chartAt ℂ z) x = y := (chartAt ℂ z).right_inv hy_target
  -- AnalyticAt at y ⇒ meromorphicOrderAt ≥ 0 at y.
  have h_nonneg : 0 ≤ meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) y :=
    hy_an.meromorphicOrderAt_nonneg
  -- Bridge to mmeromorphicOrderAt at x via chart-independence.
  have h_in_atlas : (chartAt ℂ z) ∈ atlas ℂ X := chart_mem_atlas ℂ z
  have h_order_eq : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
      = meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) x) :=
    mmeromorphicOrderAt_eq_of_isManifold h_in_atlas hx_source
  rw [h_chart_x] at h_order_eq
  have h_mmero_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    rw [h_order_eq]; exact h_nonneg
  -- f.toRS x = ↑(f.toFun x) (non-pole).
  have h_toRS_x : f.toRiemannSphere x = ((f.toFun x : ℂ) : RiemannSphere) :=
    f.toRiemannSphere_apply_of_nonneg h_mmero_nonneg
  -- Compute both sides.
  show (chartAt ℂ (f.toRiemannSphere z))
        (f.toRiemannSphere ((chartAt ℂ z).symm y))
      = (f.toFun ((chartAt ℂ z).symm y))⁻¹
  rw [show (chartAt ℂ z).symm y = x from rfl, h_toRS_x, h_chart_eq]
  show RiemannSphere.chartS (((f.toFun x : ℂ) : RiemannSphere)) = (f.toFun x)⁻¹
  exact RiemannSphere.chartSToFun_coe (f.toFun x)

/-- **Order = -1 at simple pole.** -/
theorem principalDivisorMap_toFun_eq_neg_one_at_simple_pole
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {z : X}
    (h_toRS_inf : f.toRiemannSphere z = (OnePoint.infty : RiemannSphere))
    (h_reg : z ∈ f.regularSet) :
    (principalDivisorMap f : X → ℤ) z = -1 := by
  classical
  -- Step 1: f.chartPullback z has value 0 at chart z (chartS ∞ = 0).
  have h_chart_eq : (chartAt ℂ (f.toRiemannSphere z)
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartS := by
    rw [h_toRS_inf]; rfl
  have h_value_zero : f.chartPullback z ((chartAt ℂ z) z) = 0 := by
    show (chartAt ℂ (f.toRiemannSphere z))
      (f.toRiemannSphere ((chartAt ℂ z).symm ((chartAt ℂ z) z))) = 0
    rw [(chartAt ℂ z).left_inv (mem_chart_source ℂ z), h_chart_eq, h_toRS_inf]
    exact RiemannSphere.chartS_apply_infty
  -- Step 2: AnalyticAt at chart z, deriv ≠ 0.
  have h_analyticAt : _root_.AnalyticAt ℂ (f.chartPullback z) ((chartAt ℂ z) z) :=
    f.analyticAt_chartPullback z
  have h_deriv_ne : deriv (f.chartPullback z) ((chartAt ℂ z) z) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc h_reg
  -- Step 3: analyticOrderAt = 1.
  have h_analytic_order :
      analyticOrderAt (f.chartPullback z) ((chartAt ℂ z) z) = 1 :=
    h_analyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h_value_zero h_deriv_ne
  -- Step 4: meromorphicOrderAt (f.chartPullback z) = 1.
  have h_mer_order_chartPullback :
      meromorphicOrderAt (f.chartPullback z) ((chartAt ℂ z) z) = (1 : WithTop ℤ) := by
    rw [h_analyticAt.meromorphicOrderAt_eq, h_analytic_order]
    rfl
  -- Step 5: eventual equality with (f.toFun ∘ chart.symm)⁻¹.
  have h_event_eq := f.chartPullback_eventuallyEq_inv_toFun_at_pole h_toRS_inf
  -- Step 6: meromorphicOrderAt of inv equals 1.
  have h_mer_order_inv :
      meromorphicOrderAt ((f.toFun ∘ (chartAt ℂ z).symm)⁻¹) ((chartAt ℂ z) z)
      = (1 : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr h_event_eq]
    exact h_mer_order_chartPullback
  -- Step 7: meromorphicOrderAt_inv ⇒ meromorphicOrderAt (f.toFun ∘ chart.symm) = -1.
  have h_mer_order_toFun :
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) = (-1 : ℤ) := by
    have h_inv : meromorphicOrderAt ((f.toFun ∘ (chartAt ℂ z).symm)⁻¹) ((chartAt ℂ z) z)
        = -meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) :=
      meromorphicOrderAt_inv
    rw [h_mer_order_inv] at h_inv
    have h_neg : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)
        = -(1 : WithTop ℤ) := by
      have := neg_eq_iff_eq_neg.mp h_inv.symm
      exact this
    rw [h_neg]
    rfl
  -- Step 8: conclude.
  rw [principalDivisorMap_apply]
  show JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun z = -1
  unfold JacobianChallenge.MMeromorphicOn.orderFun
  show (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun z).untop₀ = -1
  show (meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)).untop₀ = -1
  rw [h_mer_order_toFun]
  rfl

end MeromorphicNonzero

end JacobianChallenge

end
