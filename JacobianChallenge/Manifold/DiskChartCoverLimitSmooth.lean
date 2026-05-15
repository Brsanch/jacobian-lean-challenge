/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverLimitSection
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option diagnostics.threshold 100

/-! # Chart-x-frame identification of the limit section

For each base point `x ∈ basePoints` and `y ∈ X` in chart-`x.source`,
the chart-`x`-frame value of the limit section at `y` equals the
`smulRight 1` of the BCF limit `g_lim_x ⟨chart-x y, _⟩` (for y in
chart-`x` preimage of the closed inner disk).

This identifies the chart-`x`-frame representative of the limit section
with the analytic function `bcfExtend cover g_lim_x ∘ chart-x` on
chart-`x` preimage of the inner ball, giving the analyticity needed
for section smoothness.

## Main results

* `DiskChartCover.chartFrame_limit_scalar` — scalar identification at
  chart image of y.
* `DiskChartCover.chartFrame_limit_eq_smulRight` — CLM identification:
  the chart-`x`-frame CLM equals `smulRight 1 (g_lim_x ⟨chart-x y, _⟩)`
  for y in chart-`x` preimage of closed inner disk.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- A CLM `ℂ →L[ℂ] ℂ` is determined by its value at `1`. -/
private lemma clm_eq_smulRight_value_at_one (T : ℂ →L[ℂ] ℂ) :
    T = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (T 1) := by
  apply ContinuousLinearMap.ext
  intro z
  show T z = z * T 1
  rw [show z = z • (1 : ℂ) from by simp, T.map_smul]
  simp [smul_eq_mul]

/-- **Chart-frame scalar identification at `y` in chart-`x.source`.**

For each base point `x ∈ basePoints` and `y ∈ chart-x.source`, the
chart-`x`-frame value of `limitSectionToFun y` at `1` equals the BCF
limit `g_lim_x` evaluated at `chart-x y` (whenever that lies in the
inner closed disk). The hypothesis on `y` being in the chart-`x`
*preimage of the inner closed disk* (equivalent to `chart-x y ∈
closedBall (innerRadius_x)`) ensures the BCF makes sense at this
point. -/
theorem chartFrame_limit_scalar
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    {x : X} (hx : x ∈ cover.basePoints) (y : X) (hy : y ∈ (chartAt ℂ x).source)
    (hy_in_closedBall : (chartAt ℂ x) y ∈
      closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
    {g_lim_x : BoundedContinuousFunction
        ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim_x)) :
    (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y)
        (limitSectionToFun cover om_n h_diag y)) 1
      = g_lim_x ⟨(chartAt ℂ x) y, hy_in_closedBall⟩ := by
  -- Apply continuity of `coordChange (achart y) (achart x) y` to the
  -- pointwise limit, then continuity of `(· 1)` to get scalar convergence.
  have h_pointwise := limitSectionToFun_tendsto cover om_n h_diag y
  have h_cc_cont :
      Continuous ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y :
          (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)).toFun :=
    ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y) (achart ℂ x) y).continuous
  -- chart-x-frame CLM converges (composition with continuous coordChange).
  have h_clm_tendsto :
      Tendsto (fun k => ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y) ((om_n (ψ k)).toFun y)) atTop
        (𝓝 (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x) y)
          (limitSectionToFun cover om_n h_diag y))) :=
    (h_cc_cont.tendsto _).comp h_pointwise
  -- Apply `(· 1)` (continuous):
  have h_value_at_1 :
      Tendsto (fun k => (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y) ((om_n (ψ k)).toFun y)) 1) atTop
        (𝓝 ((((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ y) (achart ℂ x) y)
          (limitSectionToFun cover om_n h_diag y)) 1)) := by
    have h_app_cont : Continuous (fun T : ℂ →L[ℂ] ℂ => T 1) :=
      (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous
    exact (h_app_cont.tendsto _).comp h_clm_tendsto
  -- The scalar sequence equals `localCoeff (om_n (ψ k)) x ((chartAt ℂ x) y)`.
  have h_localCoeff_eq : ∀ k,
      (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y) ((om_n (ψ k)).toFun y)) 1
      = localCoeff (om_n (ψ k)) x ((chartAt ℂ x) y) := by
    intro k
    -- Use `localCoeff` formula at `w = (chartAt ℂ x) y`.
    have h_symm : (chartAt ℂ x).symm ((chartAt ℂ x) y) = y :=
      (chartAt ℂ x).left_inv hy
    show (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y) ((om_n (ψ k)).toFun y)) 1
        = (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
            (achart ℂ ((chartAt ℂ x).symm ((chartAt ℂ x) y)))
            (achart ℂ x)
            ((chartAt ℂ x).symm ((chartAt ℂ x) y)))
            ((om_n (ψ k)).toFun ((chartAt ℂ x).symm ((chartAt ℂ x) y)))) 1
    rw [h_symm]
  rw [show (fun k => (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y) ((om_n (ψ k)).toFun y)) 1)
        = fun k => localCoeff (om_n (ψ k)) x ((chartAt ℂ x) y) from
      funext h_localCoeff_eq] at h_value_at_1
  -- The scalar sequence converges to `g_lim_x ⟨(chartAt ℂ x) y, hy_in_closedBall⟩`
  -- by BCF point evaluation continuity composed with chip 5b's BCF convergence.
  set w_y : ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
    ⟨(chartAt ℂ x) y, hy_in_closedBall⟩ with hwy_def
  have h_eval_tendsto :
      Tendsto (fun k => (localCoeffBcf cover (om_n (ψ k)) hx) w_y) atTop
        (𝓝 (g_lim_x w_y)) :=
    (continuous_eval_const w_y).tendsto _ |>.comp h_tendsto
  have h_eval_eq : ∀ k,
      (localCoeffBcf cover (om_n (ψ k)) hx) w_y
      = localCoeff (om_n (ψ k)) x ((chartAt ℂ x) y) := by
    intro k
    rfl
  rw [show (fun k => (localCoeffBcf cover (om_n (ψ k)) hx) w_y)
        = fun k => localCoeff (om_n (ψ k)) x ((chartAt ℂ x) y) from
      funext h_eval_eq] at h_eval_tendsto
  -- Both sequences converge; the limits are equal.
  exact tendsto_nhds_unique h_value_at_1 h_eval_tendsto

/-- **Chart-frame CLM identification at `y` in chart-`x.source`.**

The chart-`x`-frame CLM at `y` of the limit section equals
`smulRight 1 (g_lim_x ⟨chart-x y, _⟩)`. -/
theorem chartFrame_limit_eq_smulRight
    (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    {x : X} (hx : x ∈ cover.basePoints) (y : X) (hy : y ∈ (chartAt ℂ x).source)
    (hy_in_closedBall : (chartAt ℂ x) y ∈
      closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
    {g_lim_x : BoundedContinuousFunction
        ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ}
    (h_tendsto :
      Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim_x)) :
    ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y) (achart ℂ x) y)
        (limitSectionToFun cover om_n h_diag y)
      = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          (g_lim_x ⟨(chartAt ℂ x) y, hy_in_closedBall⟩) := by
  have h_scalar :=
    chartFrame_limit_scalar cover om_n h_diag hx y hy hy_in_closedBall h_tendsto
  rw [clm_eq_smulRight_value_at_one
    (((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y) (achart ℂ x) y) (limitSectionToFun cover om_n h_diag y))]
  rw [h_scalar]

end DiskChartCover

end JacobianChallenge

end
