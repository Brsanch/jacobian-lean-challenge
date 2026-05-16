/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.TraceExtensionChartCoeff

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `traceExtensionChartCoeff Q k` analytic on a closed disc around `0`

`AnalyticAt ℂ (traceExtensionChartCoeff Q k) 0` from chip 3d-5 gives
analyticity *at* `0`. Bundle wiring chips need an **explicit closed
disc** around `0` on which the extension is analytic — to match it to
a chart-target ball around `(chartAt ℂ v₀) v₀`.

This file extracts a positive radius via `AnalyticAt.exists_ball_analyticOnNhd`.

No `sorry`, no `axiom`. -/

open Metric

namespace JacobianChallenge
namespace Manifold

/-- **Trace-extension chart coefficient analytic on a closed disc.**
Given `Q` analytic at `0` and `k ≥ 1`, there exists `r > 0` such that
`traceExtensionChartCoeff Q k` is `AnalyticOnNhd ℂ` on the closed
disc `closedBall 0 r`. -/
theorem traceExtensionChartCoeff_analyticOnNhd_closedBall
    {Q : ℂ → ℂ} {k : ℕ} (hQ : AnalyticAt ℂ Q 0) (hk : 1 ≤ k) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (traceExtensionChartCoeff Q k) (Metric.closedBall 0 r) := by
  have h_an : AnalyticAt ℂ (traceExtensionChartCoeff Q k) 0 :=
    traceExtensionChartCoeff_analyticAt hQ hk
  -- Get an open ball on which `traceExtensionChartCoeff Q k` is `AnalyticOnNhd`.
  obtain ⟨r, hr_pos, h_ball⟩ := h_an.exists_ball_analyticOnNhd
  -- The open `ball 0 r` contains the closed `closedBall 0 (r/2)`.
  refine ⟨r / 2, by linarith, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall] at hz
  have hz_open : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball]
    linarith
  exact h_ball z hz_open

end Manifold
end JacobianChallenge
