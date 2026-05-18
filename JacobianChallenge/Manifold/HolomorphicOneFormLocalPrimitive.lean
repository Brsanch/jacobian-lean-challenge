/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import Mathlib.Analysis.Complex.HasPrimitives

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Local primitive of a holomorphic 1-form on a chart-ball

For a holomorphic 1-form `α : HolomorphicOneForm X` and a chart base
point `y : X`, the chart-pullback coefficient `α.localCoeff y : ℂ → ℂ`
is holomorphic on the chart target. On any **open ball** contained in
the chart target, mathlib's `DifferentiableOn.isExactOn_ball` gives a
primitive `F : ℂ → ℂ` such that `HasDerivAt F (α.localCoeff y z) z` for
all `z` in the ball.

This is Step 2 of the item-14 reverse-leg arc: the local primitive
inside each chart-disk gives the path-independence of `∫_γ ω` for
piecewise-smooth loops contained in the chart-disk (by FTC on the
primitive).

## What this file ships

* `HolomorphicOneForm.exists_local_primitive_on_ball` — packaged form:
  for any `y : X` and any radius `r > 0` with `Metric.ball ((chartAt ℂ y) y) r
  ⊆ (chartAt ℂ y).target`, a primitive `F : ℂ → ℂ` of `α.localCoeff y`
  exists on the ball.

* `HolomorphicOneForm.exists_local_primitive_centered` — convenience:
  there exists some positive radius `r` and a primitive on the
  centered open ball (the radius is chosen via the chart-target
  openness).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology ContDiff
open Metric Complex

noncomputable section

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace HolomorphicOneForm

/-- **Local primitive on a chart-ball.**

For `α : HolomorphicOneForm X`, base point `y : X`, and any open ball
`Metric.ball c r ⊆ (chartAt ℂ y).target`, the chart-pullback coefficient
`α.localCoeff y` admits a primitive on the ball: there exists `F : ℂ → ℂ`
with `HasDerivAt F (α.localCoeff y z) z` for every `z ∈ Metric.ball c r`. -/
theorem exists_local_primitive_on_ball
    (α : HolomorphicOneForm X) (y : X) {c : ℂ} {r : ℝ}
    (h_sub : Metric.ball c r ⊆ (chartAt ℂ y).target) :
    IsExactOn (α.localCoeff y) (Metric.ball c r) := by
  -- α.localCoeff y is DifferentiableOn (chartAt ℂ y).target.
  have h_diff : DifferentiableOn ℂ (α.localCoeff y) (chartAt ℂ y).target :=
    α.localCoeff_differentiableOn y
  -- Restrict to the ball.
  have h_diff_ball : DifferentiableOn ℂ (α.localCoeff y) (Metric.ball c r) :=
    h_diff.mono h_sub
  -- Apply mathlib's Morera-on-disk.
  exact h_diff_ball.isExactOn_ball

/-- **Local primitive with prescribed value at a base point.** Pin the
primitive's value at any `x₀ ∈ Metric.ball c r` to any desired `y : ℂ`. -/
theorem exists_local_primitive_on_ball_with_val
    (α : HolomorphicOneForm X) (y : X) {c : ℂ} {r : ℝ}
    (h_sub : Metric.ball c r ⊆ (chartAt ℂ y).target)
    (x₀ : ℂ) (v : ℂ) :
    ∃ F : ℂ → ℂ, F x₀ = v ∧
      ∀ z ∈ Metric.ball c r, HasDerivAt F (HolomorphicOneForm.localCoeff α y z) z :=
  (exists_local_primitive_on_ball α y h_sub).with_val_at x₀ v

/-- **Centered local primitive at a chart base point.** There exists
`r > 0` such that `Metric.ball ((chartAt ℂ y) y) r ⊆ (chartAt ℂ y).target`
and `α.localCoeff y` has a primitive on this ball. -/
theorem exists_local_primitive_centered
    (α : HolomorphicOneForm X) (y : X) :
    ∃ r > (0 : ℝ),
      Metric.ball ((chartAt ℂ y) y) r ⊆ (chartAt ℂ y).target ∧
      IsExactOn (α.localCoeff y) (Metric.ball ((chartAt ℂ y) y) r) := by
  -- `(chartAt ℂ y).target` is open and contains `(chartAt ℂ y) y`.
  have h_open : IsOpen (chartAt ℂ y).target := (chartAt ℂ y).open_target
  have h_mem : (chartAt ℂ y) y ∈ (chartAt ℂ y).target :=
    (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  -- Extract a positive radius ball.
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp h_open _ h_mem
  refine ⟨r, hr_pos, hr_sub, ?_⟩
  exact exists_local_primitive_on_ball α y hr_sub

end HolomorphicOneForm

end JacobianChallenge

end
