/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartCoefficients
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option diagnostics.threshold 100

/-! # Holomorphy of `chartNCoeff` for `HolomorphicOneForm RiemannSphere`

`chartNCoeff om : ℂ → ℂ` (from `RiemannSphereChartCoefficients.lean`) is
the north-chart coefficient of a holomorphic 1-form on the Riemann
sphere, `chartNCoeff om z = om.eval ((z : RS)) 1`. This file proves
that `chartNCoeff om` is `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` on all of `ℂ`, and
hence — via the self-modeled `ContMDiff ↔ ContDiff` bridge and
`contDiff_omega_iff_analyticOnNhd` — `AnalyticOnNhd ℂ (chartNCoeff om)
Set.univ` and `Differentiable ℂ (chartNCoeff om)`. The Differentiable
form is exactly the input
`RiemannSphereGenus.Liouville_holomorphic_form_chartN_coeff` needs.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- For `x₀ ∈ chartN.source` (equivalently `x₀ ≠ ∞`), a neighbourhood of
`x₀` is entirely contained in `chartN.source`. -/
private lemma chartN_source_mem_nhds
    {x₀ : RiemannSphere} (hx₀ : x₀ ≠ (OnePoint.infty : OnePoint ℂ)) :
    chartN.source ∈ 𝓝 x₀ := by
  refine chartN.open_source.mem_nhds ?_
  rw [chartN_source]
  exact hx₀

/-- For `x : RiemannSphere` with `x ≠ ∞`, the canonical atlas chart is
`chartN`. -/
private lemma chartAt_of_ne_infty
    {x : RiemannSphere} (hx : x ≠ (OnePoint.infty : OnePoint ℂ)) :
    chartAt ℂ x = chartN := by
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe z =>
    show chartAt' ((z : RiemannSphere)) = chartN
    rw [chartAt'_coe]

/-- The chart-N coefficient of a holomorphic 1-form on the Riemann
sphere is `ContMDiff ω` from `ℂ` to `ℂ` (self-modelled). -/
theorem chartNCoeff_contMDiff (om : HolomorphicOneForm RiemannSphere) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (chartNCoeff om) := by
  intro z
  set x₀ : RiemannSphere := ((z : ℂ) : RiemannSphere) with hx₀_def
  have hx₀_ne : x₀ ≠ (OnePoint.infty : OnePoint ℂ) := by
    rw [hx₀_def]
    exact OnePoint.coe_ne_infty z
  have h_chart_x₀ : chartAt ℂ x₀ = chartN := chartAt_of_ne_infty hx₀_ne
  -- om is ContMDiff as a TotalSpace-valued section.
  have h_om_section :
      ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (fun x : RiemannSphere =>
          Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (om.toFun x)) :=
    om.contMDiff
  have h_om_at :
      ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (fun x : RiemannSphere =>
          Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (om.toFun x)) x₀ :=
    h_om_section.contMDiffAt
  -- Bridge to the chart-coordinate representation.
  rw [cotangentSection_contMDiffAt_iff om.toFun] at h_om_at
  -- The coord-change-adjusted function is eventually equal to `om.toFun`.
  have h_eq :
      (fun x : RiemannSphere =>
        (cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
          (achart ℂ x) (achart ℂ x₀) x (om.toFun x))
        =ᶠ[𝓝 x₀] (fun x : RiemannSphere => om.toFun x) := by
    filter_upwards [chartN_source_mem_nhds hx₀_ne] with x hx
    have hx_ne : x ≠ (OnePoint.infty : OnePoint ℂ) := by
      rw [chartN_source] at hx
      exact hx
    have h_chart_x : chartAt ℂ x = chartN := chartAt_of_ne_infty hx_ne
    -- achart ℂ x has value chartAt ℂ x = chartN, so both acharts are equal
    -- (as subtypes of atlas H M).
    have h_eq_achart : achart ℂ x = achart ℂ x₀ := by
      apply Subtype.ext
      rw [achart_val, achart_val, h_chart_x, h_chart_x₀]
    rw [h_eq_achart]
    -- Now apply coordChange_self.
    apply cotangentBundleCore_coordChange_self
    -- Need: x ∈ (cotangentBundleCore _ _).baseSet (achart ℂ x₀).
    -- The baseSet of the cotangent core at achart ℂ x₀ = achart ℂ x is
    -- (achart ℂ x).val.source = chartN.source. We have x ∈ chartN.source.
    show x ∈ (achart ℂ x₀).1.source
    rw [achart_val, h_chart_x₀, chartN_source]
    exact hx_ne
  have h_om_simp :
      ContMDiffAt (𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
        (fun x : RiemannSphere => om.toFun x) x₀ :=
    h_om_at.congr_of_eventuallyEq h_eq.symm
  -- Compose with `ContinuousLinearMap.apply ℂ ℂ 1`.
  have h_apply_at :
      ContMDiffAt 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
        (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) (om.toFun x₀) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiffAt
  have h_eval :
      ContMDiffAt (𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω
        (fun x : RiemannSphere =>
          ContinuousLinearMap.apply ℂ ℂ (1 : ℂ) (om.toFun x)) x₀ :=
    h_apply_at.comp x₀ h_om_simp
  -- Compose with `chartN.symm : ℂ → RS`. chartN.symm is ContMDiffOn on
  -- chartN.target = univ.
  have h_chart_symm_on :
      ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ)) ω
        (chartN.symm : ℂ → RiemannSphere) chartN.target := by
    have h := contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := x₀)
    rw [h_chart_x₀] at h
    exact h
  have hz_target : z ∈ chartN.target := by rw [chartN_target]; trivial
  have h_chart_symm_at :
      ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ)) ω
        (chartN.symm : ℂ → RiemannSphere) z :=
    h_chart_symm_on.contMDiffAt (chartN.open_target.mem_nhds hz_target)
  have h_chart_symm_z : chartN.symm z = x₀ := by
    rw [hx₀_def, chartN_symm_apply]
  -- Compose: at z, chartN.symm z = x₀ so h_eval applies.
  rw [show x₀ = chartN.symm z from h_chart_symm_z.symm] at h_eval
  have h_comp :
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        ((fun x : RiemannSphere =>
          ((ContinuousLinearMap.apply ℂ ℂ) (1 : ℂ)) (om.toFun x))
          ∘ (chartN.symm : ℂ → RiemannSphere)) z :=
    h_eval.comp z h_chart_symm_at
  -- chartNCoeff om z = om.eval (chartN.symm z) 1 = (om.toFun (chartN.symm z)) 1
  --                  = (CLM.apply ℂ ℂ 1) (om.toFun (chartN.symm z)).
  show ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (chartNCoeff om) z
  have h_funext :
      chartNCoeff om = (fun x : RiemannSphere =>
        ((ContinuousLinearMap.apply ℂ ℂ) (1 : ℂ)) (om.toFun x))
          ∘ (chartN.symm : ℂ → RiemannSphere) := by
    funext z'
    -- LHS: chartNCoeff om z' = om.eval (chartN.symm z') 1.
    -- RHS: (CLM.apply ℂ ℂ 1) (om.toFun (chartN.symm z')) = (om.toFun (chartN.symm z')) 1.
    show om.eval (chartN.symm z') 1
        = ((ContinuousLinearMap.apply ℂ ℂ) (1 : ℂ)) (om.toFun (chartN.symm z'))
    rw [ContinuousLinearMap.apply_apply]
    rfl
  rw [h_funext]
  exact h_comp

/-- The chart-N coefficient is `ContDiff ω` over `ℂ`, self-modelled. -/
theorem chartNCoeff_contDiff (om : HolomorphicOneForm RiemannSphere) :
    ContDiff ℂ ω (chartNCoeff om) :=
  (chartNCoeff_contMDiff om).contDiff

/-- The chart-N coefficient is `AnalyticOnNhd ℂ (chartNCoeff om) Set.univ`. -/
theorem chartNCoeff_analyticOnNhd (om : HolomorphicOneForm RiemannSphere) :
    AnalyticOnNhd ℂ (chartNCoeff om) Set.univ :=
  contDiff_omega_iff_analyticOnNhd.mp (chartNCoeff_contDiff om)

/-- The chart-N coefficient is `AnalyticAt ℂ` at every point of `ℂ`. -/
theorem chartNCoeff_analyticAt
    (om : HolomorphicOneForm RiemannSphere) (z : ℂ) :
    AnalyticAt ℂ (chartNCoeff om) z :=
  chartNCoeff_analyticOnNhd om z (Set.mem_univ z)

/-- The chart-N coefficient is `Differentiable ℂ` on all of `ℂ` (entire). -/
theorem chartNCoeff_differentiable (om : HolomorphicOneForm RiemannSphere) :
    Differentiable ℂ (chartNCoeff om) :=
  fun z => (chartNCoeff_analyticAt om z).differentiableAt

end RiemannSphere

end JacobianChallenge
