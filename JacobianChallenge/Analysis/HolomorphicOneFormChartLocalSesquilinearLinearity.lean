/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalSesquilinear
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqWeightedFinite
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Linearity in the left argument of `chartLocalSesquilinear`

Ships the chart-local linearity fields needed to package
`globalPettersonHermitian` as a `HermitianOnHolomorphicOneForm`.

## What ships

* `chartLocalSesquilinearIntegrand_integrableOn_target_of_subordinate` —
  the chart-local integrand is `IntegrableOn` the chart target when
  the weight `χ : X → ℝ` is continuous and `tsupport χ` ⊆ chart source
  on a compact `X`.
* `chartLocalSesquilinear_smul_left` — ℂ-linearity in the left
  argument (unconditional via `integral_smul`).
* `chartLocalSesquilinear_add_left_of_integrableOn` — additivity in
  the left argument given integrability of both summands' integrands.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Complex Set

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Integrability of the chart-local integrand -/

/-- **Integrability of the chart-local sesquilinear integrand.** -/
theorem chartLocalSesquilinearIntegrand_integrableOn_target_of_subordinate
    (om eta : HolomorphicOneForm X) (y : X) {χ : X → ℝ}
    (hχ_cont : Continuous χ)
    (h_tsupp_sub : tsupport χ ⊆ (chartAt ℂ y).source) :
    IntegrableOn
      (fun z : ℂ => (χ ((chartAt ℂ y).symm z) : ℂ)
        * localCoeff om y z * starRingEnd ℂ (localCoeff eta y z))
      (chartAt ℂ y).target (volume : Measure ℂ) := by
  set K : Set ℂ := chartAt ℂ y '' tsupport χ with hK_def
  have h_tsupp_compact : IsCompact (tsupport χ) := isClosed_closure.isCompact
  have hK_compact : IsCompact K :=
    h_tsupp_compact.image_of_continuousOn
      ((chartAt ℂ y).continuousOn.mono h_tsupp_sub)
  have hK_sub : K ⊆ (chartAt ℂ y).target := by
    rw [hK_def]
    intro w hw
    obtain ⟨x, hx_in, hxw⟩ := hw
    rw [← hxw]
    exact (chartAt ℂ y).map_source (h_tsupp_sub hx_in)
  set g : ℂ → ℂ := fun z =>
    (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
      * starRingEnd ℂ (localCoeff eta y z) with hg_def
  -- g vanishes on (target \ K).
  have h_vanish : ∀ z ∈ (chartAt ℂ y).target \ K, g z = 0 := by
    intro z ⟨hz_target, hz_notK⟩
    have h_symm_not_tsupp : (chartAt ℂ y).symm z ∉ tsupport χ := by
      intro h_in
      apply hz_notK
      rw [hK_def]
      refine ⟨(chartAt ℂ y).symm z, h_in, ?_⟩
      exact (chartAt ℂ y).right_inv hz_target
    have h_symm_not_supp : (chartAt ℂ y).symm z ∉ Function.support χ :=
      fun h => h_symm_not_tsupp (subset_closure h)
    have h_χ_zero : χ ((chartAt ℂ y).symm z) = 0 := by
      by_contra hne
      exact h_symm_not_supp hne
    show (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
          * starRingEnd ℂ (localCoeff eta y z) = 0
    rw [h_χ_zero]; simp
  -- Continuity of g on chart-target.
  have h_chart_symm_cont : ContinuousOn (chartAt ℂ y).symm (chartAt ℂ y).target :=
    (chartAt ℂ y).continuousOn_symm
  have h_lc_om_cont : ContinuousOn (localCoeff om y) (chartAt ℂ y).target :=
    (localCoeff_analyticOn om y).continuousOn
  have h_lc_eta_cont : ContinuousOn (localCoeff eta y) (chartAt ℂ y).target :=
    (localCoeff_analyticOn eta y).continuousOn
  have h_conj_cont : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  have hg_cont_on : ContinuousOn g (chartAt ℂ y).target := by
    rw [hg_def]
    refine ContinuousOn.mul (ContinuousOn.mul ?_ h_lc_om_cont) ?_
    · have h_cast_cont : Continuous (fun r : ℝ => (r : ℂ)) := Complex.continuous_ofReal
      exact (h_cast_cont.comp hχ_cont).comp_continuousOn h_chart_symm_cont
    · exact h_conj_cont.comp_continuousOn h_lc_eta_cont
  -- IntegrableOn on the compact subset K via ContinuousOn.integrableOn_compact.
  have h_intK : IntegrableOn g K (volume : Measure ℂ) :=
    (hg_cont_on.mono hK_sub).integrableOn_compact hK_compact
  -- IntegrableOn on (chart-target \ K): g = 0 there, so integrable.
  have h_diff_meas : MeasurableSet ((chartAt ℂ y).target \ K) :=
    (chartAt ℂ y).open_target.measurableSet.diff hK_compact.measurableSet
  have h_intDiff : IntegrableOn g ((chartAt ℂ y).target \ K) (volume : Measure ℂ) := by
    -- g =ᵐ[vol.restrict (target \ K)] (fun _ => 0).
    have h_ae_eq : (fun _ : ℂ => (0 : ℂ))
        =ᵐ[(volume : Measure ℂ).restrict ((chartAt ℂ y).target \ K)] g := by
      rw [Filter.EventuallyEq, ae_restrict_iff' h_diff_meas]
      filter_upwards with z hz using (h_vanish z hz).symm
    exact (integrable_zero ℂ ℂ _).congr h_ae_eq
  -- Combine via IntegrableOn.union; chart-target = K ∪ (chart-target \ K).
  have h_int_union :
      IntegrableOn g (K ∪ ((chartAt ℂ y).target \ K)) (volume : Measure ℂ) :=
    h_intK.union h_intDiff
  have h_eq : K ∪ ((chartAt ℂ y).target \ K) = (chartAt ℂ y).target :=
    Set.union_diff_cancel hK_sub
  rw [h_eq] at h_int_union
  exact h_int_union

/-! ## ℂ-linearity in the left argument (unconditional) -/

/-- **ℂ-linearity in the left argument** of the chart-local Hermitian
sesquilinear pairing. Unconditional via `MeasureTheory.integral_smul`. -/
theorem chartLocalSesquilinear_smul_left
    (c : ℂ) (om eta : HolomorphicOneForm X) (y : X) (χ : X → ℝ) :
    chartLocalSesquilinear (c • om) eta y χ
      = c * chartLocalSesquilinear om eta y χ := by
  unfold chartLocalSesquilinear
  rw [show (fun z : ℂ => (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff (c • om) y z
            * starRingEnd ℂ (localCoeff eta y z))
        = (fun z : ℂ => c * ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
            * starRingEnd ℂ (localCoeff eta y z))) from ?_]
  · -- ∫ c * f = c * ∫ f.
    exact MeasureTheory.integral_const_mul c _
  · funext z
    rw [HolomorphicOneForm.localCoeff_smul]
    show (χ ((chartAt ℂ y).symm z) : ℂ) * (c • localCoeff om y z)
          * starRingEnd ℂ (localCoeff eta y z)
        = c * ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om y z
            * starRingEnd ℂ (localCoeff eta y z))
    rw [smul_eq_mul]; ring

/-! ## Additivity in the left argument (conditional on integrability) -/

/-- **Additivity in the left argument** of the chart-local Hermitian
sesquilinear pairing, given integrability of both summands' integrands.
-/
theorem chartLocalSesquilinear_add_left_of_integrableOn
    (om₁ om₂ eta : HolomorphicOneForm X) (y : X) (χ : X → ℝ)
    (h_int₁ : IntegrableOn
      (fun z : ℂ => (χ ((chartAt ℂ y).symm z) : ℂ)
        * localCoeff om₁ y z * starRingEnd ℂ (localCoeff eta y z))
      (chartAt ℂ y).target (volume : Measure ℂ))
    (h_int₂ : IntegrableOn
      (fun z : ℂ => (χ ((chartAt ℂ y).symm z) : ℂ)
        * localCoeff om₂ y z * starRingEnd ℂ (localCoeff eta y z))
      (chartAt ℂ y).target (volume : Measure ℂ)) :
    chartLocalSesquilinear (om₁ + om₂) eta y χ
      = chartLocalSesquilinear om₁ eta y χ + chartLocalSesquilinear om₂ eta y χ := by
  unfold chartLocalSesquilinear
  rw [show (fun z : ℂ => (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff (om₁ + om₂) y z
            * starRingEnd ℂ (localCoeff eta y z))
        = (fun z : ℂ =>
            ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om₁ y z
                * starRingEnd ℂ (localCoeff eta y z))
            + ((χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om₂ y z
                * starRingEnd ℂ (localCoeff eta y z))) from ?_]
  · -- ∫ (f + g) = ∫ f + ∫ g, given Integrable f and g.
    exact MeasureTheory.integral_add h_int₁ h_int₂
  · funext z
    rw [HolomorphicOneForm.localCoeff_add]
    show (χ ((chartAt ℂ y).symm z) : ℂ)
          * (localCoeff om₁ y z + localCoeff om₂ y z)
          * starRingEnd ℂ (localCoeff eta y z)
        = (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om₁ y z
              * starRingEnd ℂ (localCoeff eta y z)
          + (χ ((chartAt ℂ y).symm z) : ℂ) * localCoeff om₂ y z
              * starRingEnd ℂ (localCoeff eta y z)
    ring

end HolomorphicOneForm

end
