/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverLimitPackage
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import Mathlib.Topology.ContinuousMap.Bounded.Basic

set_option linter.unusedSectionVars false

/-! # `localCoeffBcf` compatibility for `limitHolomorphicOneForm`

For the limit form built by `limitHolomorphicOneForm`, its restriction
to the inner closed disk via `localCoeffBcf` equals the chosen BCF limit
`(h_diag x hx).choose`. This is the bridge to feed the existing
`tendsto_ofForm_of_tendsto_localCoeffBcf` for the Riesz finale.

No `sorry`, no `axiom`.
-/

open Set Metric Filter Topology

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- Pointwise: the limit form's `localCoeff` at the chart-image is the
pointwise limit of the sequence's `localCoeff` values. -/
private lemma localCoeff_limit_tendsto
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    {x : X} (_hx : x ∈ cover.basePoints) (w : ℂ) :
    Tendsto (fun k => HolomorphicOneForm.localCoeff (om_n (ψ k)) x w)
      atTop (𝓝 (HolomorphicOneForm.localCoeff
        (cover.limitHolomorphicOneForm om_n h_diag) x w)) := by
  -- Pointwise limit of section values at q := (chartAt x).symm w.
  have h_pt := cover.limitSectionToFun_tendsto om_n (ψ := ψ) h_diag
    ((chartAt ℂ x).symm w)
  -- `localCoeff om x w` is, by definition, `(coordChange ... om.toFun(symm w)) 1`.
  -- The map `v ↦ ((coordChange ... q) v) 1` is continuous (CLM evaluation at 1
  -- composed with a fixed CLM applied to v).
  have h_cont : Continuous (fun v : ℂ →L[ℂ] ℂ =>
      (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ ((chartAt ℂ x).symm w)) (achart ℂ x)
          ((chartAt ℂ x).symm w) : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) v) 1) :=
    ((ContinuousLinearMap.apply ℂ ℂ 1).continuous).comp
      (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ x).symm w)) (achart ℂ x)
        ((chartAt ℂ x).symm w))).continuous
  -- Apply h_cont to h_pt.
  have h_comp := (h_cont.tendsto _).comp h_pt
  -- The composition expression matches `localCoeff (om_n (ψ k)) x w → localCoeff (limit) x w`.
  show Tendsto
    (fun k => (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ x).symm w)) (achart ℂ x)
        ((chartAt ℂ x).symm w) ((om_n (ψ k)).toFun
          ((chartAt ℂ x).symm w))) 1))
    atTop
    (𝓝 (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ x).symm w)) (achart ℂ x)
        ((chartAt ℂ x).symm w)
        ((cover.limitHolomorphicOneForm om_n h_diag).toFun
          ((chartAt ℂ x).symm w))) 1))
  rw [cover.limitHolomorphicOneForm_toFun]
  exact h_comp

/-- **Compatibility lemma**: `localCoeffBcf` of `limitHolomorphicOneForm`
equals the chosen BCF limit. -/
theorem localCoeffBcf_limitHolomorphicOneForm
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffBcf cover (cover.limitHolomorphicOneForm om_n h_diag) hx
      = (h_diag x hx).choose := by
  -- Two BCFs equal iff equal as functions.
  apply DFunLike.ext
  intro w
  rw [localCoeffBcf_apply]
  -- BCF tendsto ⇒ uniform tendsto ⇒ pointwise tendsto at w.
  have h_bcf_tendsto := (h_diag x hx).choose_spec
  have h_uniform := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    h_bcf_tendsto
  have h_pt_seq :
      Tendsto (fun k => (localCoeffBcf cover (om_n (ψ k)) hx) w)
        atTop (𝓝 ((h_diag x hx).choose w)) := h_uniform.tendsto_at w
  simp only [localCoeffBcf_apply] at h_pt_seq
  -- Pointwise limit also goes to LHS via the continuity bridge.
  have h_pt_limit := cover.localCoeff_limit_tendsto om_n h_diag hx w.1
  -- Conclude by uniqueness of limits.
  exact tendsto_nhds_unique h_pt_limit h_pt_seq

end DiskChartCover

end JacobianChallenge

end
