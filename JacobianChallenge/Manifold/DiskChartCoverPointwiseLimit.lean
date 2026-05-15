/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverDiagonal

set_option diagnostics.threshold 100

/-! # Scalar limit of `localCoeff` at chart image of any base point's preimage

From chip 5c's diagonal subsequence (convergent in the
`BoundedContinuousFunction` metric at every base point), for every
`y ∈ X` we extract a *scalar* limit by evaluating the BCF at the chart
image of `y` via any base point `x_y` with `y` in the chart-`x_y`
preimage of `ball (innerRadius_{x_y})`.

This gives a function `chartLimitScalar cover h_diag y : ℂ` such that
`localCoeff (om_n (ψ k)) x_y ((chartAt ℂ x_y) y) → chartLimitScalar y`.

The full CLM-valued pointwise limit + section construction is a further
chip; this is the scalar foundation.

## Main result

* `DiskChartCover.chartLimit_tendsto` — for each `y ∈ X`, the scalar
  sequence `(om_n (ψ k).toFun y) 1` viewed via the chosen base point's
  chart converges.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm Filter

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- For any `y : X`, pick a base point `x ∈ basePoints` with `y` in
the chart-`x` preimage of `ball (innerRadius_x)`. -/
noncomputable def chosenBasePoint (cover : DiskChartCover X) (y : X) : X :=
  (cover.covers y).choose

omit [IsManifold 𝓘(ℂ) ω X] in
lemma chosenBasePoint_mem (cover : DiskChartCover X) (y : X) :
    chosenBasePoint cover y ∈ cover.basePoints :=
  (cover.covers y).choose_spec.1

omit [IsManifold 𝓘(ℂ) ω X] in
lemma chosenBasePoint_source (cover : DiskChartCover X) (y : X) :
    y ∈ (chartAt ℂ (chosenBasePoint cover y)).source :=
  (cover.covers y).choose_spec.2.1

omit [IsManifold 𝓘(ℂ) ω X] in
lemma chosenBasePoint_chartImage_in_ball (cover : DiskChartCover X) (y : X) :
    (chartAt ℂ (chosenBasePoint cover y)) y ∈
      ball ((chartAt ℂ (chosenBasePoint cover y)) (chosenBasePoint cover y))
        (cover.innerRadius (chosenBasePoint cover y)) :=
  (cover.covers y).choose_spec.2.2

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The chart image of `y` is in the inner closed disk. -/
private lemma chartImage_in_innerDisk (cover : DiskChartCover X) (y : X) :
    (chartAt ℂ (chosenBasePoint cover y)) y ∈
      closedBall ((chartAt ℂ (chosenBasePoint cover y)) (chosenBasePoint cover y))
        (cover.innerRadius (chosenBasePoint cover y)) :=
  ball_subset_closedBall (chosenBasePoint_chartImage_in_ball cover y)

/-- The chart image of `y` packaged as an element of the subtype. -/
private noncomputable def chartImageSubtype (cover : DiskChartCover X) (y : X) :
    ↥(closedBall
        ((chartAt ℂ (chosenBasePoint cover y)) (chosenBasePoint cover y))
        (cover.innerRadius (chosenBasePoint cover y))) :=
  ⟨(chartAt ℂ (chosenBasePoint cover y)) y, chartImage_in_innerDisk cover y⟩

/-- **Chart-frame scalar limit**: at every `y ∈ X`, the scalar sequence
`localCoeff (om_n (ψ k)) (chosenBasePoint y) ((chartAt ℂ (chosenBasePoint y)) y)`
converges. -/
theorem chartLimit_tendsto (cover : DiskChartCover X) [Nonempty X]
    (om_n : ℕ → HolomorphicOneForm X)
    {ψ : ℕ → ℕ}
    (h_diag : ∀ (x : X) (hx : x ∈ cover.basePoints),
      ∃ g_lim : BoundedContinuousFunction
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) ℂ,
        Tendsto (fun k => localCoeffBcf cover (om_n (ψ k)) hx) atTop (𝓝 g_lim))
    (y : X) :
    ∃ c : ℂ,
      Tendsto (fun k => localCoeff (om_n (ψ k)) (chosenBasePoint cover y)
        ((chartAt ℂ (chosenBasePoint cover y)) y)) atTop (𝓝 c) := by
  set x_y := chosenBasePoint cover y with hxy_def
  have hxy_mem : x_y ∈ cover.basePoints := chosenBasePoint_mem cover y
  obtain ⟨g_lim_xy, h_tendsto⟩ := h_diag x_y hxy_mem
  set w_y : ↥(closedBall ((chartAt ℂ x_y) x_y) (cover.innerRadius x_y)) :=
    chartImageSubtype cover y with hwy_def
  refine ⟨g_lim_xy w_y, ?_⟩
  have h_eval :
      Tendsto (fun k => (localCoeffBcf cover (om_n (ψ k)) hxy_mem) w_y)
        atTop (𝓝 (g_lim_xy w_y)) :=
    (continuous_eval_const w_y).tendsto _ |>.comp h_tendsto
  -- Identify `(localCoeffBcf ...) w_y` with `localCoeff ... (chartAt y)`.
  convert h_eval using 1

end DiskChartCover

end JacobianChallenge

end
