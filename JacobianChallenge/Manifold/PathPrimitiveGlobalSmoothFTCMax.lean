/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamedMax

set_option linter.unusedSectionVars false

/-! # Global `pathPrimitive` smoothness + FTC under a maxAtlas chart-cover admissibility

Maximal-atlas variant of `PathPrimitiveGlobalSmoothFTC.lean`. Same
shape, with the per-chart smoothness/FTC named hypotheses replaced by
their Max counterparts and the chart-cover atlas-membership replaced
by maxAtlas membership.

This is the global pendant of the local Max chain
(steps 1-3c of HANDOFF_ITEM14.md cascade): if every point of `X` is
covered by a chart in the ℝ-⊤ maximal atlas with convex target on
which both `ChartLocalPrimitiveSmoothExtMax` and
`ChartLocalPrimitiveFTCMax` hold for `om`, then under
`LoopPeriodVanishes om x₀`, `pathPrimitive om` is globally
`ContMDiff ω` and satisfies the global FTC at every `x : X`.

The maxAtlas form lets the cover be discharged unconditionally on
arbitrary X via `convexBallChartAt y` (which has convex target by
construction, lies in the ℝ-⊤ maximal atlas, and now — per
`ChartLocalPrimitiveSmoothExtMaxConvexBallChartAt.lean` +
`ChartLocalPrimitiveFTCMaxConvexBallChartAt.lean` — admits both named
hypotheses unconditionally).

## What this file ships

* `PathPrimitiveAdmissibleChartCoverMax om` — maxAtlas admissibility
  predicate.
* `pathPrimitive_contMDiff_of_admissibleMax` — global `ContMDiff ω`.
* `pathPrimitive_eval_eq_mfderiv_of_admissibleMax` — global FTC.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Maximal-atlas admissibility predicate.** At every point `x : X`,
there is a chart `φ` in the ℝ-`⊤` maximal atlas with convex target,
a chart-basepoint `y ∈ φ.source`, and `x ∈ φ.source`, such that the
Max-form chart-local primitive smoothness and FTC named hypotheses
hold. -/
def PathPrimitiveAdmissibleChartCoverMax
    (om : HolomorphicOneForm X) : Prop :=
  ∀ x : X, ∃ (φ : OpenPartialHomeomorph X ℂ)
    (h_max : φ ∈ IsManifold.maximalAtlas (𝓘(ℝ, ℂ)) ⊤ X)
    (h_target_convex : Convex ℝ φ.target) (y : X) (hy : y ∈ φ.source),
    x ∈ φ.source ∧
      ChartLocalPrimitiveSmoothExtMax φ h_max h_target_convex y hy om ∧
      ChartLocalPrimitiveFTCMax φ h_max h_target_convex y hy om

/-- **Global `ContMDiff ω` of `pathPrimitive` under maxAtlas admissibility +
`LoopPeriodVanishes`.** -/
theorem pathPrimitive_contMDiff_of_admissibleMax
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (h_admit : PathPrimitiveAdmissibleChartCoverMax om) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) := by
  intro x
  obtain ⟨φ, h_max, h_target_convex, y, hy, hx, h_smooth_ext, _⟩ :=
    h_admit x
  have h_on :=
    pathPrimitive_contMDiffOn_source_of_ChartLocalPrimitiveSmoothExtMax
      h_conn x₀ om h_loop φ h_max h_target_convex y hy h_smooth_ext
  have h_within : ContMDiffWithinAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (pathPrimitive h_conn x₀ om) φ.source x :=
    h_on x hx
  exact h_within.contMDiffAt (φ.open_source.mem_nhds hx)

/-- **Global FTC: `om.eval x = mfderiv pathPrimitive x`** under maxAtlas
admissibility + `LoopPeriodVanishes`. -/
theorem pathPrimitive_eval_eq_mfderiv_of_admissibleMax
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (h_admit : PathPrimitiveAdmissibleChartCoverMax om)
    (x : X) :
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ om) x := by
  obtain ⟨φ, h_max, h_target_convex, y, hy, hx, h_smooth_ext, h_ftc⟩ :=
    h_admit x
  exact mfderiv_pathPrimitive_eq_eval_on_source_of_ChartLocalPrimitiveFTCMax
    h_conn x₀ om h_loop φ h_max h_target_convex y hy h_smooth_ext h_ftc x hx

end JacobianChallenge

end
