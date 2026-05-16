/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzManifoldFibreRegular
import JacobianChallenge.Manifold.ChartPullbackAnalyticAtTarget

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold f-regularity at Hurwitz fibre points — AnalyticAt-discharged

Composes chip 3d-19 (manifold f-regularity, takes AnalyticAt hypothesis)
with chip 3d-21 (ZZ24, chart-pullback AnalyticAt on chart target).

The AnalyticAt hypothesis from chip 3d-19 is discharged by ZZ24,
leaving only:

* `w ∈ (chartAt ℂ z₀).target`
* `f.toRiemannSphere ((chartAt ℂ z₀).symm w) ∈ (chartAt ℂ (f z₀)).source`
* `deriv (f.chartPullback z₀) w ≠ 0`

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold f-regularity at a chart-target point (AnalyticAt discharged).** -/
theorem manifold_fibre_regular_at_chart_point_unconditional
    (f : MeromorphicNonzero X) (z₀ : X)
    {w : ℂ}
    (h_target : w ∈ (chartAt ℂ z₀).target)
    (h_f_src : f.toRiemannSphere ((chartAt ℂ z₀).symm w)
      ∈ (chartAt ℂ (f.toRiemannSphere z₀)).source)
    (h_g_deriv_ne : deriv (f.chartPullback z₀) w ≠ 0) :
    (chartAt ℂ z₀).symm w ∈ f.regularSet :=
  f.manifold_fibre_regular_at_chart_point z₀ h_target
    (f.chartPullback_analyticAt_of_chart_target z₀ h_target h_f_src)
    h_g_deriv_ne

end MeromorphicNonzero
end JacobianChallenge

end
