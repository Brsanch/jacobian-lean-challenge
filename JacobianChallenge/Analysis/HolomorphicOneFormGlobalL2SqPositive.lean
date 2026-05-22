/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormGlobalL2Sq
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqPositiveBall
import JacobianChallenge.Analysis.HolomorphicOneFormLocalCoeffAtPoint
import JacobianChallenge.Analysis.RealModelManifoldFromComplex
import JacobianChallenge.Topology.SubsingletonFromPrimitiveExistence
import Mathlib.Topology.Compactness.LocallyFinite

/-! # Positivity of the global Petersson L²-square norm

Headline: `om ≠ 0 ⇒ 0 < globalPettersonL2Sq om f` for any smooth
partition of unity `f` subordinate to the chart-source cover of a
compact connected complex 1-manifold.

No `sorry`, no `axiom`. -/

set_option linter.unusedSectionVars false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Set

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Headline: the global Petersson L²-square norm is strictly positive
for a nonzero holomorphic 1-form.** -/
theorem globalPettersonL2Sq_pos_of_ne_zero
    (om : HolomorphicOneForm X) (h_ne : om ≠ 0)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X))
    (hf_subord : f.IsSubordinate (fun y : X => (chartAt ℂ y).source)) :
    0 < globalPettersonL2Sq om f := by
  -- Step 1: pick x₀ with om.eval x₀ ≠ 0.
  have h_eval_exists : ∃ x : X, om.eval x ≠ 0 := by
    by_contra h_no
    apply h_ne
    apply (JacobianChallenge.HolomorphicOneForm.eq_zero_iff_eval_at_one om).mpr
    intro x
    have : om.eval x = 0 := by
      by_contra hx; exact h_no ⟨x, hx⟩
    rw [this]; rfl
  obtain ⟨x₀, hx₀_ne⟩ := h_eval_exists
  -- Step 2: pick y₀ with f y₀ x₀ > 0.
  obtain ⟨y₀, hy₀_pos⟩ := f.exists_pos_of_mem (Set.mem_univ x₀)
  -- Step 3: x₀ ∈ chart-source y₀ via subordinacy.
  have hx₀_source : x₀ ∈ (chartAt ℂ y₀).source := by
    have h_in_support : x₀ ∈ Function.support (fun x => (f y₀) x) := hy₀_pos.ne'
    have h_in_tsupport : x₀ ∈ tsupport (f y₀) := subset_closure h_in_support
    exact hf_subord y₀ h_in_tsupport
  set z₀ : ℂ := (chartAt ℂ y₀) x₀ with hz₀_def
  have hz₀_target : z₀ ∈ (chartAt ℂ y₀).target := by
    rw [hz₀_def]; exact (chartAt ℂ y₀).map_source hx₀_source
  -- Step 4: localCoeff om y₀ z₀ ≠ 0.
  have h_loc_ne : localCoeff om y₀ z₀ ≠ 0 := by
    rw [hz₀_def]
    exact localCoeff_at_chart_image_ne_zero_of_eval_ne_zero om hx₀_source hx₀_ne
  -- Step 5: ‖localCoeff‖ ≥ c_form on a nhd of z₀.
  have h_form_pos : 0 < ‖localCoeff om y₀ z₀‖ := norm_pos_iff.mpr h_loc_ne
  set c_form : ℝ := ‖localCoeff om y₀ z₀‖ / 2 with hc_form_def
  have hc_form_pos : 0 < c_form := by rw [hc_form_def]; linarith
  have h_loc_cont_on : ContinuousOn (localCoeff om y₀) (chartAt ℂ y₀).target :=
    (localCoeff_analyticOn om y₀).continuousOn
  have h_loc_cont_at : ContinuousAt (fun z => ‖localCoeff om y₀ z‖) z₀ := by
    have h_cont_at_lc : ContinuousAt (localCoeff om y₀) z₀ :=
      (h_loc_cont_on z₀ hz₀_target).continuousAt
        ((chartAt ℂ y₀).open_target.mem_nhds hz₀_target)
    exact h_cont_at_lc.norm
  have h_form_eventually : ∀ᶠ z in 𝓝 z₀, c_form < ‖localCoeff om y₀ z‖ := by
    have h_target_lt : c_form < ‖localCoeff om y₀ z₀‖ := by rw [hc_form_def]; linarith
    exact h_loc_cont_at.tendsto.eventually (Ioi_mem_nhds h_target_lt)
  -- Step 5b: f y₀ ∘ (chartAt ℂ y₀).symm ≥ c_chi on a nhd of z₀.
  set c_chi : ℝ := (f y₀) x₀ / 2 with hc_chi_def
  have hc_chi_pos : 0 < c_chi := by rw [hc_chi_def]; linarith
  have h_chi_cont_at : ContinuousAt (fun z => (f y₀) ((chartAt ℂ y₀).symm z)) z₀ := by
    have h_chi_cont_global : Continuous (fun x => (f y₀) x) :=
      (f.toFun y₀).contMDiff.continuous
    have h_symm_cont_at : ContinuousAt (chartAt ℂ y₀).symm z₀ :=
      ((chartAt ℂ y₀).continuousOn_symm z₀ hz₀_target).continuousAt
        ((chartAt ℂ y₀).open_target.mem_nhds hz₀_target)
    exact h_chi_cont_global.continuousAt.comp h_symm_cont_at
  have h_chi_at_z₀ : (f y₀) ((chartAt ℂ y₀).symm z₀) = (f y₀) x₀ := by
    rw [hz₀_def, (chartAt ℂ y₀).left_inv hx₀_source]
  have h_chi_eventually : ∀ᶠ z in 𝓝 z₀, c_chi < (f y₀) ((chartAt ℂ y₀).symm z) := by
    have h_target_lt : c_chi < (f y₀) ((chartAt ℂ y₀).symm z₀) := by
      rw [h_chi_at_z₀, hc_chi_def]; linarith
    exact h_chi_cont_at.tendsto.eventually (Ioi_mem_nhds h_target_lt)
  have h_target_eventually : ∀ᶠ z in 𝓝 z₀, z ∈ (chartAt ℂ y₀).target :=
    (chartAt ℂ y₀).open_target.mem_nhds hz₀_target
  have h_combined : ∀ᶠ z in 𝓝 z₀,
      z ∈ (chartAt ℂ y₀).target ∧
      c_form < ‖localCoeff om y₀ z‖ ∧
      c_chi < (f y₀) ((chartAt ℂ y₀).symm z) :=
    h_target_eventually.and (h_form_eventually.and h_chi_eventually)
  obtain ⟨ε', hε'_pos, hε'_ball⟩ := Metric.eventually_nhds_iff_ball.mp h_combined
  -- Step 6: lower bound on integrand on ball z₀ ε'.
  have h_lower_bound : ∀ z ∈ Metric.ball z₀ ε',
      ENNReal.ofReal c_chi * (ENNReal.ofReal c_form)^2
        ≤ ENNReal.ofReal ((f y₀) ((chartAt ℂ y₀).symm z))
            * (‖localCoeff om y₀ z‖₊ : ℝ≥0∞)^2 := by
    intro z hz
    obtain ⟨_h_in_target, h_form_gt, h_chi_gt⟩ := hε'_ball z hz
    have h_form_le : ENNReal.ofReal c_form ≤ (‖localCoeff om y₀ z‖₊ : ℝ≥0∞) := by
      have h_step : ENNReal.ofReal c_form ≤ ENNReal.ofReal ‖localCoeff om y₀ z‖ :=
        ENNReal.ofReal_le_ofReal (le_of_lt h_form_gt)
      have h_eq : ENNReal.ofReal ‖localCoeff om y₀ z‖
          = (‖localCoeff om y₀ z‖₊ : ℝ≥0∞) :=
        (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)).trans (by rfl)
      rwa [h_eq] at h_step
    have h_chi_le : ENNReal.ofReal c_chi
        ≤ ENNReal.ofReal ((f y₀) ((chartAt ℂ y₀).symm z)) :=
      ENNReal.ofReal_le_ofReal (le_of_lt h_chi_gt)
    have h_pow : (ENNReal.ofReal c_form)^2 ≤ (‖localCoeff om y₀ z‖₊ : ℝ≥0∞)^2 :=
      pow_le_pow_left' h_form_le 2
    exact mul_le_mul' h_chi_le h_pow
  have h_weighted_lower :
      ENNReal.ofReal c_chi * (ENNReal.ofReal c_form)^2
        * (volume : Measure ℂ) (Metric.ball z₀ ε')
      ≤ chartLocalL2SqWeighted om y₀ (fun x => (f y₀) x) := by
    unfold chartLocalL2SqWeighted
    calc ENNReal.ofReal c_chi * (ENNReal.ofReal c_form)^2
            * (volume : Measure ℂ) (Metric.ball z₀ ε')
        = ∫⁻ _ in Metric.ball z₀ ε',
            ENNReal.ofReal c_chi * (ENNReal.ofReal c_form)^2
              ∂(volume : Measure ℂ) := by rw [setLIntegral_const]
      _ ≤ ∫⁻ z in Metric.ball z₀ ε',
              ENNReal.ofReal ((f y₀) ((chartAt ℂ y₀).symm z))
                * (‖localCoeff om y₀ z‖₊ : ℝ≥0∞)^2 ∂(volume : Measure ℂ) := by
            refine setLIntegral_mono_ae' Metric.isOpen_ball.measurableSet ?_
            exact Filter.Eventually.of_forall h_lower_bound
      _ ≤ ∫⁻ z in (chartAt ℂ y₀).target,
              ENNReal.ofReal ((f y₀) ((chartAt ℂ y₀).symm z))
                * (‖localCoeff om y₀ z‖₊ : ℝ≥0∞)^2 ∂(volume : Measure ℂ) := by
            refine lintegral_mono_set ?_
            intro z hz
            exact (hε'_ball z hz).1
  have h_lower_bound_pos :
      0 < ENNReal.ofReal c_chi * (ENNReal.ofReal c_form)^2
        * (volume : Measure ℂ) (Metric.ball z₀ ε') := by
    have h_chi_pos_e : 0 < ENNReal.ofReal c_chi := ENNReal.ofReal_pos.mpr hc_chi_pos
    have h_form_pos_e : 0 < ENNReal.ofReal c_form := ENNReal.ofReal_pos.mpr hc_form_pos
    have h_form_sq_pos : 0 < (ENNReal.ofReal c_form)^2 :=
      (pow_ne_zero 2 h_form_pos_e.ne').bot_lt
    have h_vol_pos : 0 < (volume : Measure ℂ) (Metric.ball z₀ ε') :=
      Metric.measure_ball_pos volume z₀ hε'_pos
    have h_first : 0 < ENNReal.ofReal c_chi * (ENNReal.ofReal c_form)^2 :=
      ENNReal.mul_pos h_chi_pos_e.ne' h_form_sq_pos.ne'
    exact ENNReal.mul_pos h_first.ne' h_vol_pos.ne'
  have h_weighted_pos : 0 < chartLocalL2SqWeighted om y₀ (fun x => (f y₀) x) :=
    h_lower_bound_pos.trans_le h_weighted_lower
  -- Step 7: finsum lower bound by single positive term.
  -- The set {y | tsupport (f y) ≠ ∅} = {y | support (f y) ≠ ∅} is finite via locallyFinite + compact.
  have h_lf_support : LocallyFinite (fun y : X => Function.support (fun x => (f y) x)) :=
    f.locallyFinite
  have h_finite_active : {y : X | (Function.support (fun x => (f y) x)).Nonempty}.Finite :=
    h_lf_support.finite_nonempty_of_compact
  -- Support of y ↦ chartLocalL2SqWeighted om y (f y) is ⊆ {y | support (f y).Nonempty}.
  have h_finsupp :
      Set.Finite (Function.support
        (fun y : X => chartLocalL2SqWeighted om y (fun x => (f y) x))) := by
    refine h_finite_active.subset ?_
    intro y hy
    -- hy : chartLocalL2SqWeighted om y (f y) ≠ 0.
    -- Need: support (f y) is nonempty.
    by_contra h_empty
    apply hy
    -- h_empty : y ∉ {y | (support (f y)).Nonempty} ⇒ support (f y) = ∅ ⇒ f y ≡ 0.
    have h_not_nonempty : ¬ (Function.support (fun x => (f y) x)).Nonempty := h_empty
    have h_support_empty : Function.support (fun x => (f y) x) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at h_not_nonempty
      exact h_not_nonempty
    have h_fy_zero : (fun x => (f y) x) = fun _ => 0 := by
      rw [Function.support_eq_empty_iff] at h_support_empty
      exact h_support_empty
    -- f y ≡ 0 ⇒ weighted integral is 0.
    show chartLocalL2SqWeighted om y (fun x => (f y) x) = 0
    unfold chartLocalL2SqWeighted
    have h_zero : ∀ z, ENNReal.ofReal ((fun x => (f y) x) ((chartAt ℂ y).symm z))
          * (‖localCoeff om y z‖₊ : ℝ≥0∞)^2 = 0 := by
      intro z
      rw [h_fy_zero]
      simp
    simp [h_zero]
  -- Apply single_le_finsum.
  unfold globalPettersonL2Sq
  have h_single_le :
      chartLocalL2SqWeighted om y₀ (fun x => (f y₀) x)
      ≤ ∑ᶠ y, chartLocalL2SqWeighted om y (fun x => (f y) x) :=
    single_le_finsum y₀ h_finsupp (fun _ => zero_le _)
  exact h_weighted_pos.trans_le h_single_le

end HolomorphicOneForm

end
