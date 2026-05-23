/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartLocalPrimitiveFTCChartAt
import JacobianChallenge.Manifold.ChartLocalPrimitiveSmoothExtChartAt
import JacobianChallenge.Manifold.HasAdmissibleChartCoverClass

set_option linter.unusedSectionVars false

/-! # Chart-cover lift: `HasAdmissibleChartCover X` from convex `chartAt` targets

Combines chip C (`chartLocalPrimitiveSmoothExt_chartAt`) and chip D
(`chartLocalPrimitiveFTC_chartAt`) into a class-driven discharge of
`PathPrimitiveAdmissibleChartCover om` for **every**
`om : HolomorphicOneForm X`, under the structural typeclass

  `HasConvexChartAtTarget X : ∀ x : X, Convex ℝ (chartAt ℂ x).target`.

The downstream payoff via the existing
`HasAdmissibleChartCoverClass.lean` infrastructure is:

* `pathPrimitive_contMDiff_of_HasAdmissibleChartCover` — global
  `ContMDiff ω` of `pathPrimitive` for any `om` with
  `LoopPeriodVanishes om x₀`;
* `pathPrimitive_eval_eq_mfderiv_of_HasAdmissibleChartCover` — global
  FTC `om.eval x = mfderiv (pathPrimitive om) x` likewise.

These are exactly the per-basis `h_smooth_b` + `h_ftc_b` inputs of
`genus_eq_zero_iff_homeo_from_4_minimal_inputs` (item 14 entry point),
once `LoopPeriodVanishes` is supplied by `BasedSmoothLoopsBoundHypothesis`
(= `h_bslb`) on a simply-connected `X`.

After this chip, the two genuinely remaining item-14 minimal hypotheses
on `X` with `HasConvexChartAtTarget` are `hSP` (RR-class) and `h_bslb`
(smooth-Hurewicz). No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasConvexChartAtTarget X`**: every `chartAt ℂ x` has convex target.

Structural property of the manifold's atlas. True for the standard
two-chart atlas on `RiemannSphere` (both `chartN.target`, `chartS.target`
are `Set.univ`) and for the standard `chartAt` on the complex torus
`ℂ ⧸ L` (target is an open disc inside a fundamental domain). -/
class HasConvexChartAtTarget : Prop where
  /-- Per-point witness. -/
  convex : ∀ x : X, Convex ℝ (chartAt ℂ x).target

variable {X}

/-! ## `PathPrimitiveAdmissibleChartCover om` for any `om` -/

/-- **`PathPrimitiveAdmissibleChartCover om` UNCONDITIONAL under
`[HasConvexChartAtTarget X]`** for any `om : HolomorphicOneForm X`.

The chart cover is the per-point `chartAt ℂ x` itself (its target is
convex by the hypothesis). Chip C discharges
`ChartLocalPrimitiveSmoothExt` and chip D discharges
`ChartLocalPrimitiveFTC` at that chart unconditionally. -/
theorem pathPrimitiveAdmissibleChartCover_of_HasConvexChartAtTarget
    [HasConvexChartAtTarget X] (om : HolomorphicOneForm X) :
    PathPrimitiveAdmissibleChartCover om := by
  intro x
  refine ⟨chartAt ℂ x, chart_mem_atlas ℂ x,
    HasConvexChartAtTarget.convex x, x, mem_chart_source ℂ x,
    mem_chart_source ℂ x, ?_, ?_⟩
  · -- ChartLocalPrimitiveSmoothExt via chip C.
    exact chartLocalPrimitiveSmoothExt_chartAt x
      (HasConvexChartAtTarget.convex x) om
  · -- ChartLocalPrimitiveFTC via chip D5.
    exact chartLocalPrimitiveFTC_chartAt x
      (HasConvexChartAtTarget.convex x) om

/-! ## Typeclass instance: `HasAdmissibleChartCover X` -/

/-- **`HasAdmissibleChartCover X` instance from `[HasConvexChartAtTarget X]`**
(UNCONDITIONAL, no `Subsingleton ω` hypothesis). Strictly stronger
than the existing
`instHasAdmissibleChartCoverOfConvexCoverAndSubsingletonOmega`, which
required the zero-form simplification. -/
instance instHasAdmissibleChartCoverOfConvexChartAtTarget
    [HasConvexChartAtTarget X] : HasAdmissibleChartCover X :=
  ⟨fun om => pathPrimitiveAdmissibleChartCover_of_HasConvexChartAtTarget om⟩

end JacobianChallenge

end
