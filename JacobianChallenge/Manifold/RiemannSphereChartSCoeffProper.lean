/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartNHolomorphy
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option diagnostics.threshold 100

/-! # The proper chartS-frame coefficient and its continuity at `0`

`chartSCoeffProper om w` is the chartS-frame coefficient of a holomorphic
1-form `om` on the Riemann sphere, evaluated at the canonical basis
vector `1 : ℂ`. Concretely it is the value of the cotangent-bundle
local trivialisation at `∞` applied to `(chartS.symm w, om.toFun
(chartS.symm w))`, projected via the snd component and applied to `1`.

At `w = 0`, `chartS.symm 0 = ∞`, the trivialisation at `∞` uses chartS
as its reference frame, and the coordinate change `chartS → chartS` is
the identity, so `chartSCoeffProper om 0 = om.eval ∞ 1`. This is the
form's "native" value at `∞`.

For `w ≠ 0`, the trivialisation transports `om.toFun ((w⁻¹ : ℂ) : RS)`
from the chartN-frame to the chartS-frame via the cotangent transition,
producing the classical formula `-chartNCoeff om w⁻¹ / w^2` (proved in
the companion overlap-formula chip).

This file proves the **continuity at `0`** part — exactly the (i)
condition of `R1Witness` — via the cotangent-section ContMDiff bridge
at `∞`, parallel to `RiemannSphereChartNHolomorphy.lean`'s argument for
`chartNCoeff`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- The proper chartS-frame coefficient: the cotangent bundle's
local-trivialisation at `∞` applied to `om`'s value at `chartS.symm w`,
evaluated at `1 : ℂ`. -/
noncomputable def chartSCoeffProper
    (om : HolomorphicOneForm RiemannSphere) : ℂ → ℂ :=
  fun w =>
    ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
        (achart ℂ (chartS.symm w))
        (achart ℂ (OnePoint.infty : OnePoint ℂ))
        (chartS.symm w)
        (om.toFun (chartS.symm w))) (1 : ℂ)

/-- For `x : RiemannSphere` with `x = ∞`, the canonical atlas chart is
`chartS`. -/
private lemma chartAt_infty :
    chartAt ℂ (OnePoint.infty : OnePoint ℂ) = chartS := by
  show chartAt' (OnePoint.infty : OnePoint ℂ) = chartS
  rw [chartAt'_infty]

/-- At `w = 0`, `chartSCoeffProper om 0 = om.eval ∞ 1`. -/
theorem chartSCoeffProper_zero (om : HolomorphicOneForm RiemannSphere) :
    chartSCoeffProper om 0 = om.eval (OnePoint.infty : OnePoint ℂ) 1 := by
  unfold chartSCoeffProper
  -- chartS.symm 0 = ∞.
  have h_symm : chartS.symm (0 : ℂ) = (OnePoint.infty : OnePoint ℂ) :=
    chartS_symm_apply_zero
  rw [h_symm]
  -- coordChange (achart ∞) (achart ∞) ∞ ξ = ξ via coordChange_self.
  have h_mem : (OnePoint.infty : OnePoint ℂ) ∈
      (cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).baseSet
        (achart ℂ (OnePoint.infty : OnePoint ℂ)) := by
    -- baseSet of the achart is (achart).val.source = chartAt.source.
    show (OnePoint.infty : OnePoint ℂ) ∈ (achart ℂ (OnePoint.infty : OnePoint ℂ)).1.source
    rw [achart_val, chartAt_infty]
    -- chartS.source = {x | x ≠ some 0}, and ∞ ≠ some 0.
    rw [chartS_source]
    exact fun h => OnePoint.infty_ne_coe (0 : ℂ) h
  rw [cotangentBundleCore_coordChange_self _ h_mem]
  rfl

/-- For `x₀ = ∞`, a neighbourhood of `x₀` is entirely contained in
`chartS.source`. -/
private lemma chartS_source_mem_nhds_infty :
    chartS.source ∈ 𝓝 (OnePoint.infty : OnePoint ℂ) := by
  refine chartS.open_source.mem_nhds ?_
  rw [chartS_source]
  exact fun h => OnePoint.infty_ne_coe (0 : ℂ) h

/-- `chartSCoeffProper om` is `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` at `w = 0`.

The argument is parallel to `chartNCoeff_contMDiff` but at `∞` in the
chartS frame. -/
theorem chartSCoeffProper_contMDiffAt_zero
    (om : HolomorphicOneForm RiemannSphere) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (chartSCoeffProper om) 0 := by
  set x₀ : RiemannSphere := (OnePoint.infty : OnePoint ℂ) with hx₀_def
  have h_chart_x₀ : chartAt ℂ x₀ = chartS := chartAt_infty
  -- om's contMDiff_toFun as a TotalSpace section.
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
  rw [cotangentSection_contMDiffAt_iff om.toFun] at h_om_at
  -- So `fun x => coordChange (achart x) (achart x₀) x (om.toFun x)` is
  -- ContMDiffAt at x₀ = ∞. Compose with apply 1 to get ContMDiffAt at ∞
  -- of `fun x => chartS-frame-coeff-at-x`, then with chartS.symm to get
  -- ContMDiffAt 0 of chartSCoeffProper.
  -- Compose with `ContinuousLinearMap.apply ℂ ℂ 1`.
  have h_apply_at :
      ContMDiffAt 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
        (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ))
        ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
          (achart ℂ x₀) (achart ℂ x₀) x₀ (om.toFun x₀)) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiffAt
  have h_eval :
      ContMDiffAt (𝓘(ℂ, ℂ)) 𝓘(ℂ, ℂ) ω
        (fun x : RiemannSphere =>
          ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
            ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
              (achart ℂ x) (achart ℂ x₀) x (om.toFun x))) x₀ :=
    h_apply_at.comp x₀ h_om_at
  -- Compose with chartS.symm : ℂ → RS, ContMDiff at 0 (in chartS.target).
  have h_chart_symm_on :
      ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ)) ω
        (chartS.symm : ℂ → RiemannSphere) chartS.target := by
    have h := contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := x₀)
    rw [h_chart_x₀] at h
    exact h
  have h0_target : (0 : ℂ) ∈ chartS.target := by
    rw [chartS_target]; trivial
  have h_chart_symm_at :
      ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ)) ω
        (chartS.symm : ℂ → RiemannSphere) 0 :=
    h_chart_symm_on.contMDiffAt (chartS.open_target.mem_nhds h0_target)
  have h_chart_symm_z : chartS.symm (0 : ℂ) = x₀ := chartS_symm_apply_zero
  rw [show x₀ = chartS.symm (0 : ℂ) from h_chart_symm_z.symm] at h_eval
  have h_comp :
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
        ((fun x : RiemannSphere =>
          ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
            ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
              (achart ℂ x) (achart ℂ (chartS.symm (0 : ℂ))) x (om.toFun x)))
          ∘ (chartS.symm : ℂ → RiemannSphere)) 0 :=
    h_eval.comp 0 h_chart_symm_at
  -- chartSCoeffProper unfolds to match (after `apply_apply`).
  show ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (chartSCoeffProper om) 0
  -- chartS.symm 0 = ∞, so rewrite the achart in h_comp.
  have h_symm0 : chartS.symm (0 : ℂ) = (OnePoint.infty : OnePoint ℂ) :=
    chartS_symm_apply_zero
  rw [h_symm0] at h_comp
  have h_funext :
      chartSCoeffProper om = (fun x : RiemannSphere =>
        ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
          ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
            (achart ℂ x) (achart ℂ (OnePoint.infty : OnePoint ℂ)) x (om.toFun x)))
          ∘ (chartS.symm : ℂ → RiemannSphere) := by
    funext w
    show ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
            (achart ℂ (chartS.symm w))
            (achart ℂ (OnePoint.infty : OnePoint ℂ))
            (chartS.symm w)
            (om.toFun (chartS.symm w))) (1 : ℂ)
        = ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ))
            ((cotangentBundleCore (𝓘(ℂ, ℂ)) RiemannSphere).coordChange
              (achart ℂ (chartS.symm w))
              (achart ℂ (OnePoint.infty : OnePoint ℂ))
              (chartS.symm w)
              (om.toFun (chartS.symm w))))
    rw [ContinuousLinearMap.apply_apply]
  rw [h_funext]
  exact h_comp

/-- `chartSCoeffProper om` is `ContinuousAt 0`. -/
theorem chartSCoeffProper_continuousAt_zero
    (om : HolomorphicOneForm RiemannSphere) :
    ContinuousAt (chartSCoeffProper om) 0 :=
  (chartSCoeffProper_contMDiffAt_zero om).continuousAt

end RiemannSphere

end JacobianChallenge
