/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveGlobalSmoothFTCMax
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothExtMaxConvexBallChartAt
import JacobianChallenge.Manifold.ChartLocalPrimitiveFTCMaxConvexBallChartAt

set_option linter.unusedSectionVars false

/-! # `PathPrimitiveAdmissibleChartCoverMax` UNCONDITIONALLY on arbitrary X

Discharges the maximal-atlas admissibility predicate

  `PathPrimitiveAdmissibleChartCoverMax om`

unconditionally on arbitrary compact connected complex 1-manifold X,
for every `om : HolomorphicOneForm X`.

For each `x : X`, the witness is the convex-ball chart centered at `x`:

  `φ := convexBallChartAt x`,
  `h_max := convexBallChartAt_mem_maximalAtlas_real x`,
  `h_target_convex := convexBallChartAt_target_convex x`,
  `y := x`,  `hy := convexBallChartAt_x_mem_source x`.

The membership `x ∈ φ.source` is by `convexBallChartAt_x_mem_source x`.
The smoothness named hypothesis follows from
`chartLocalPrimitiveSmoothExtMax_convexBallChartAt x om` (step 4b
SmoothExt). The FTC named hypothesis follows from
`chartLocalPrimitiveFTCMax_convexBallChartAt x om` (step 4b FTC).

This is the cascade payoff. Composing with the global theorems from
`PathPrimitiveGlobalSmoothFTCMax.lean` gives, on arbitrary X under
`LoopPeriodVanishes om x₀`, both:
* `ContMDiff ω (pathPrimitive om)` globally;
* `om.eval x = mfderiv (pathPrimitive om) x` at every `x : X`.

These two are the substantive analytic content needed by the
`subsingleton_of_primitiveExistence` route to `S2ImpliesGenus0 X`.

## What this file ships

* `pathPrimitiveAdmissibleChartCoverMax_holds` — the unconditional
  discharge for every `om`.
* `pathPrimitive_contMDiff_unconditional` — corollary: global
  `ContMDiff ω` of `pathPrimitive om` under `LoopPeriodVanishes`,
  with no admissibility hypothesis.
* `pathPrimitive_eval_eq_mfderiv_unconditional` — corollary: global
  FTC under `LoopPeriodVanishes`, with no admissibility hypothesis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The maxAtlas admissibility predicate holds unconditionally** for
every `om : HolomorphicOneForm X` on arbitrary X. Witness: the convex-ball
chart `convexBallChartAt x` centered at each `x : X`. -/
theorem pathPrimitiveAdmissibleChartCoverMax_holds
    (om : HolomorphicOneForm X) :
    PathPrimitiveAdmissibleChartCoverMax om := by
  intro x
  refine ⟨convexBallChartAt x,
    convexBallChartAt_mem_maximalAtlas_real x,
    convexBallChartAt_target_convex x,
    x,
    convexBallChartAt_x_mem_source x,
    convexBallChartAt_x_mem_source x,
    ?_, ?_⟩
  · exact chartLocalPrimitiveSmoothExtMax_convexBallChartAt x om
  · exact chartLocalPrimitiveFTCMax_convexBallChartAt x om

/-- **Global `ContMDiff ω` of `pathPrimitive om` unconditionally** on
arbitrary X under `LoopPeriodVanishes`. Composes the unconditional
admissibility discharge with the global maxAtlas theorem. -/
theorem pathPrimitive_contMDiff_unconditional
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) :=
  pathPrimitive_contMDiff_of_admissibleMax h_conn x₀ om h_loop
    (pathPrimitiveAdmissibleChartCoverMax_holds om)

/-- **Global FTC unconditionally** on arbitrary X under
`LoopPeriodVanishes`: `om.eval x = mfderiv (pathPrimitive om) x` at
every `x : X`. -/
theorem pathPrimitive_eval_eq_mfderiv_unconditional
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (x : X) :
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ om) x :=
  pathPrimitive_eval_eq_mfderiv_of_admissibleMax h_conn x₀ om h_loop
    (pathPrimitiveAdmissibleChartCoverMax_holds om) x

end JacobianChallenge

end
