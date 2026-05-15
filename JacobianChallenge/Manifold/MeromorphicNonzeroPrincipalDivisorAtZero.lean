/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import JacobianChallenge.Manifold.MeromorphicNonzeroPrincipalDivisorOffFiber
import JacobianChallenge.Manifold.MeromorphicExtensionValue
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Order = 1 at simple zero — step 7d-b

At a regular point `z` with `f.toRiemannSphere z = ((0 : ℂ) : RiemannSphere)`,
`(principalDivisorMap f).toFun z = 1`. The proof works directly with the
chart-pullback `f.toFun ∘ (chartAt ℂ z).symm` (which is `mmeromorphicOrderAt`'s
underlying function), showing:

* It's analytic at `chart z` (regular + continuous bridge).
* Its value at `chart z` is `f.toFun z = 0`.
* Its derivative at `chart z` is nonzero (via the eventual equality with
  `f.chartPullback z` and the existing `deriv_chartPullback_ne_zero_of_regular`).

Then `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero` ⇒ order = 1.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Locally near `chart z`, `f.chartPullback z` and `f.toFun ∘ chart.symm`
agree, provided `f.toRiemannSphere z` is a finite point (so `chart-of-RS`
is `RiemannSphere.chartN`, which inverts `some`). -/
private lemma chartPullback_eventuallyEq_toFun_at_finite
    (f : MeromorphicNonzero X) {z : X} {w : ℂ}
    (h_toRS_some : f.toRiemannSphere z = ((w : ℂ) : RiemannSphere)) :
    f.chartPullback z =ᶠ[𝓝 ((chartAt ℂ z) z)] f.toFun ∘ (chartAt ℂ z).symm := by
  -- The RiemannSphere chart at f.toRS z (= ↑w) is `chartN` definitionally.
  have h_chart_eq : (chartAt ℂ (f.toRiemannSphere z)
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartN := by
    rw [h_toRS_some]; rfl
  -- f.toRS is continuous, so the preimage of the open set
  -- `Set.range OnePoint.some` (= "≠ ∞") under f.toRS is open in X and contains z.
  have hf_cont : Continuous f.toRiemannSphere :=
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f).continuous
  have h_range_some_open : IsOpen (Set.range (OnePoint.some : ℂ → RiemannSphere)) :=
    OnePoint.isOpen_range_coe
  have h_pre_open : IsOpen (f.toRiemannSphere ⁻¹'
      (Set.range (OnePoint.some : ℂ → RiemannSphere))) :=
    h_range_some_open.preimage hf_cont
  have h_z_mem : z ∈ f.toRiemannSphere ⁻¹'
      (Set.range (OnePoint.some : ℂ → RiemannSphere)) := by
    show f.toRiemannSphere z ∈ Set.range (OnePoint.some : ℂ → RiemannSphere)
    rw [h_toRS_some]; exact ⟨w, rfl⟩
  -- Intersect with chart.source for a nbhd of z that's also inside chart.
  have h_nbhd : (chartAt ℂ z).source ∩
      f.toRiemannSphere ⁻¹' (Set.range (OnePoint.some : ℂ → RiemannSphere)) ∈ 𝓝 z :=
    Filter.inter_mem (chart_source_mem_nhds ℂ z) (h_pre_open.mem_nhds h_z_mem)
  -- Push through chart to nbhd of chart z.
  have h_nbhd_image : (chartAt ℂ z) '' ((chartAt ℂ z).source ∩
      f.toRiemannSphere ⁻¹' (Set.range (OnePoint.some : ℂ → RiemannSphere))) ∈
      𝓝 ((chartAt ℂ z) z) := by
    rw [← (chartAt ℂ z).map_nhds_eq (mem_chart_source ℂ z)]
    exact Filter.image_mem_map h_nbhd
  -- Express eventual equality.
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nbhd_image, ?_⟩
  rintro y ⟨x, ⟨hx_source, hx_finite⟩, hxy⟩
  -- y = chart x, with x ∈ chart.source and f.toRS x ∈ range some.
  -- Goal: f.chartPullback z y = (f.toFun ∘ chart.symm) y.
  obtain ⟨v, hv'⟩ : ∃ v : ℂ, ((v : ℂ) : RiemannSphere) = f.toRiemannSphere x := hx_finite
  have hv : f.toRiemannSphere x = ((v : ℂ) : RiemannSphere) := hv'.symm
  -- Unfold chartPullback.
  show (chartAt ℂ (f.toRiemannSphere z))
        (f.toRiemannSphere ((chartAt ℂ z).symm y))
      = f.toFun ((chartAt ℂ z).symm y)
  -- (chart z).symm y = x (since y = chart x and x ∈ chart.source).
  have h_symm_y : (chartAt ℂ z).symm y = x := by
    rw [← hxy]; exact (chartAt ℂ z).left_inv hx_source
  rw [h_symm_y, hv, h_chart_eq, RiemannSphere.chartN_apply_coe]
  -- Now goal: v = f.toFun x. Recover from hv: f.toRS x = ↑v = ↑(f.toFun x) (when non-pole).
  -- f.toRS x ≠ ∞ (since it's ↑v).
  have h_x_ne_inf : f.toRiemannSphere x ≠ (OnePoint.infty : RiemannSphere) := by
    rw [hv]; exact OnePoint.coe_ne_infty v
  have h_x_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
    by_contra h_neg
    push Not at h_neg
    exact h_x_ne_inf (f.toRiemannSphere_apply_of_neg h_neg)
  have h_x_some : f.toRiemannSphere x = ((f.toFun x : ℂ) : RiemannSphere) :=
    f.toRiemannSphere_apply_of_nonneg h_x_nonneg
  -- Combining h_x_some with hv: ↑v = ↑(f.toFun x), so v = f.toFun x.
  have : ((v : ℂ) : RiemannSphere) = ((f.toFun x : ℂ) : RiemannSphere) := hv ▸ h_x_some
  exact OnePoint.coe_injective this

/-- The chart pullback of `f.toFun` (the "underlying" `mmeromorphicOrderAt`
function) is analytic at `chart z` when `0 ≤ mmeromorphicOrderAt f.toFun z`.
This uses `MeromorphicAt + ContinuousAt → AnalyticAt`. -/
private lemma toFun_chartPullback_analyticAt_of_nonneg
    (f : MeromorphicNonzero X) {z : X}
    (h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun z) :
    _root_.AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) := by
  -- Meromorphic at chart z (from f.meromorphic).
  have h_mer : MeromorphicAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) :=
    f.meromorphic z (Set.mem_univ z)
  -- Continuous at chart z (from f.regular_continuousAt + chart.symm continuity).
  have h_f_cont : ContinuousAt f.toFun z := f.regular_continuousAt z h_nonneg
  have h_chart_symm_cont : ContinuousAt (chartAt ℂ z).symm ((chartAt ℂ z) z) := by
    apply ((chartAt ℂ z).continuousOn_symm).continuousAt
    exact (chartAt ℂ z).open_target.mem_nhds (mem_chart_target ℂ z)
  have h_cont : ContinuousAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) := by
    apply ContinuousAt.comp
    · rw [(chartAt ℂ z).left_inv (mem_chart_source ℂ z)]; exact h_f_cont
    · exact h_chart_symm_cont
  -- MeromorphicAt + ContinuousAt → AnalyticAt.
  exact h_mer.analyticAt h_cont

/-- **Order = 1 at a simple zero.** -/
theorem principalDivisorMap_toFun_eq_one_at_simple_zero
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {z : X}
    (h_toRS_zero : f.toRiemannSphere z = (((0 : ℂ) : RiemannSphere)))
    (h_reg : z ∈ f.regularSet) :
    (principalDivisorMap f : X → ℤ) z = 1 := by
  classical
  -- Step 1: f.toFun z = 0 (since f.toRS z = ↑0 = ↑(f.toFun z) at a non-pole).
  have h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun z := by
    by_contra h_neg
    push Not at h_neg
    have : f.toRiemannSphere z = (OnePoint.infty : RiemannSphere) :=
      f.toRiemannSphere_apply_of_neg h_neg
    rw [h_toRS_zero] at this
    exact OnePoint.coe_ne_infty (0 : ℂ) this
  have h_toFun_zero : f.toFun z = 0 := by
    have : f.toRiemannSphere z = ((f.toFun z : ℂ) : RiemannSphere) :=
      f.toRiemannSphere_apply_of_nonneg h_nonneg
    rw [h_toRS_zero] at this
    exact (OnePoint.coe_injective this).symm
  -- Step 2: f.toFun ∘ chart.symm is analytic at chart z.
  have h_analyticAt : _root_.AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ z).symm)
      ((chartAt ℂ z) z) := f.toFun_chartPullback_analyticAt_of_nonneg h_nonneg
  -- Step 3: value at chart z is 0.
  have h_value_zero : (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) = 0 := by
    show f.toFun ((chartAt ℂ z).symm ((chartAt ℂ z) z)) = 0
    rw [(chartAt ℂ z).left_inv (mem_chart_source ℂ z), h_toFun_zero]
  -- Step 4: deriv at chart z is nonzero — via eventual equality with f.chartPullback.
  have h_eventEq : f.chartPullback z =ᶠ[𝓝 ((chartAt ℂ z) z)]
      f.toFun ∘ (chartAt ℂ z).symm :=
    f.chartPullback_eventuallyEq_toFun_at_finite h_toRS_zero
  have h_deriv_chartPullback_ne :
      deriv (f.chartPullback z) ((chartAt ℂ z) z) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc h_reg
  have h_deriv_eq :
      deriv (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)
      = deriv (f.chartPullback z) ((chartAt ℂ z) z) :=
    h_eventEq.symm.deriv_eq
  have h_deriv_ne :
      deriv (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0 := by
    rw [h_deriv_eq]; exact h_deriv_chartPullback_ne
  -- Step 5: analyticOrderAt = 1.
  have h_analytic_order :
      analyticOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) = 1 :=
    h_analyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h_value_zero h_deriv_ne
  -- Step 6: meromorphicOrderAt = 1.
  have h_mer_order :
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) =
        (1 : WithTop ℤ) := by
    rw [h_analyticAt.meromorphicOrderAt_eq]
    rw [h_analytic_order]
    rfl
  -- Step 7: conclude.
  rw [principalDivisorMap_apply]
  show JacobianChallenge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun z = 1
  unfold JacobianChallenge.MMeromorphicOn.orderFun
  show (mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun z).untop₀ = 1
  show (meromorphicOrderAt (f.toFun ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z)).untop₀ = 1
  rw [h_mer_order]
  rfl

end MeromorphicNonzero

end JacobianChallenge

end
