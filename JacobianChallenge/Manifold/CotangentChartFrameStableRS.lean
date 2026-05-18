/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PointwiseChartEvalFromFrameStability
import JacobianChallenge.Manifold.RiemannSphere

set_option linter.unusedSectionVars false

/-! # `CotangentChartFrameStable` is automatic on `RiemannSphere`
    for chart-contained loops with `basePoint ≠ ∞`

On the Riemann sphere, `chartAt ℂ x = chartN` for every `x ≠ ∞`
(`chartAt'_coe`). For a `ChartContainedClosedLoop` with `basePoint ≠ ∞`,
the loop's ambient extension stays in `(chartAt ℂ basePoint).source =
chartN.source = {x | x ≠ ∞}` (by the `ambient_in_source` field of the
structure), so every `γ.ambient t` (for `t ∈ [0, 1]`) also has
`chartAt ℂ (γ.ambient t) = chartN = chartAt ℂ basePoint`.

Combined with `pointwiseChartEvalIdentity_of_frameStable` (and hence
`chartContainedLoopVanishingHypothesis_of_frameStable`), this gives
`ChartContainedLoopVanishingHypothesis RiemannSphere` from a structural
hypothesis on basepoints — no genus-0 subsingleton needed.

## What this file ships

* `chartAt_eq_chartN_of_ne_infty` — public re-export of the
  `RiemannSphereChartNHolomorphy.chartAt_of_ne_infty` private lemma.
* `cotangentChartFrameStable_RiemannSphere` — every chart-contained
  closed loop on RS with `basePoint ≠ ∞` is frame-stable.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open Complex

namespace JacobianChallenge

namespace RiemannSphere

/-- **Public re-export.** For `x : RiemannSphere` with `x ≠ ∞`, the
canonical atlas chart is `chartN`. -/
lemma chartAt_eq_chartN_of_ne_infty
    {x : RiemannSphere} (hx : x ≠ (OnePoint.infty : OnePoint ℂ)) :
    chartAt ℂ x = chartN := by
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe z =>
    show chartAt' ((z : RiemannSphere)) = chartN
    rw [chartAt'_coe]

end RiemannSphere

namespace ChartContainedClosedLoop

/-- **Frame stability is automatic for chart-contained loops on `RS`
with `basePoint ≠ ∞`.** Both `chartAt ℂ basePoint` and
`chartAt ℂ (γ.ambient t)` equal `chartN`. -/
theorem cotangentChartFrameStable_RiemannSphere
    (data : ChartContainedClosedLoop (X := RiemannSphere))
    (h_ne_infty : data.basePoint ≠ (OnePoint.infty : OnePoint ℂ)) :
    CotangentChartFrameStable data := by
  intro t ht
  -- `chartAt ℂ basePoint = chartN`.
  have h_base : chartAt ℂ data.basePoint = RiemannSphere.chartN :=
    RiemannSphere.chartAt_eq_chartN_of_ne_infty h_ne_infty
  -- `γ.ambient t ∈ (chartAt ℂ basePoint).source = chartN.source = {x | x ≠ ∞}`.
  have h_in_source : data.γ.ambient t ∈ (chartAt ℂ data.basePoint).source :=
    data.ambient_in_source t ht
  -- Convert to `x ≠ ∞`.
  rw [h_base, RiemannSphere.chartN_source] at h_in_source
  have h_amb_ne_infty :
      data.γ.ambient t ≠ (OnePoint.infty : OnePoint ℂ) := h_in_source
  -- `chartAt ℂ (γ.ambient t) = chartN = chartAt ℂ basePoint`.
  rw [RiemannSphere.chartAt_eq_chartN_of_ne_infty h_amb_ne_infty,
      ← h_base]

/-! ## Per-loop discharge of complex period vanishing on `RS` -/

/-- **Per-loop vanishing.** For a chart-contained closed loop on
`RiemannSphere` with `basePoint ≠ ∞` and any holomorphic 1-form,
`complexChainPeriod (single γ) α = 0`. Combines frame stability
(`cotangentChartFrameStable_RiemannSphere`) with the
`PointwiseChartEvalIdentity` discharge and the local-primitive FTC
machinery. -/
theorem complexChainPeriod_vanishes_RiemannSphere
    (data : ChartContainedClosedLoop (X := RiemannSphere))
    (h_ne_infty : data.basePoint ≠ (OnePoint.infty : OnePoint ℂ))
    (α : HolomorphicOneForm RiemannSphere) :
    complexChainPeriod (SmoothChain.single data.γ) α = 0 := by
  -- Frame stability for this loop.
  have h_stable : CotangentChartFrameStable data :=
    cotangentChartFrameStable_RiemannSphere data h_ne_infty
  -- Discharge of PointwiseChartEvalIdentity for this (data, α).
  have h_point : PointwiseChartEvalIdentity data α :=
    pointwiseChartEvalIdentity_of_frameStable data α h_stable
  -- Discharge of ℂ-integrand continuity.
  have h_cont : ContinuousOn
      (fun t : ℝ => (α.eval (data.γ.ambient t)) (data.γ.velocity t))
      (Set.Icc (0 : ℝ) 1) :=
    complexEvalIntegrand_continuousOn data.γ α
  -- Compose to get the integral-level bridge, then plug into the
  -- chart-contained-loop discharge.
  have h_bridge : ComplexChainPeriodEqChartIntegral_named data α :=
    complexChainPeriodEqChartIntegral_from_pointwise data α h_point h_cont
  -- Rewrite via bridge, apply chartPath_loop_integral_zero.
  rw [h_bridge]
  apply chartPath_loop_integral_zero data α
  -- Interval integrability of the chart-coord integrand.
  have h1 := data.localCoeff_chartPath_continuousOn α
  have h2 := derivChartPathContinuousOn_holds data
  exact (h1.mul h2).intervalIntegrable_of_Icc zero_le_one

end ChartContainedClosedLoop

end JacobianChallenge

end
