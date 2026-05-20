/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PathPrimitiveLocalSmoothFTCNamed

set_option linter.unusedSectionVars false

/-! # Global `pathPrimitive` smoothness + FTC under a chart-cover admissibility

This file composes the local chart-bridge from
`PathPrimitiveLocalSmoothFTCNamed.lean` into a **global** statement: if
the manifold `X` is covered by convex-target charts on each of which
the named analytic hypotheses
(`ChartLocalPrimitiveSmoothExt` + `ChartLocalPrimitiveFTC`) hold for
`om`, then **under `LoopPeriodVanishes om x₀`**, `pathPrimitive om` is
globally `ContMDiff ω` and satisfies the global FTC
`om.eval x = mfderiv (pathPrimitive om) x` at every `x : X`.

The "admissibility" predicate bundles three things:

1. a chart cover (every `x : X` is in some chart `φ`);
2. convex target for each such chart (precondition of
   `chartLocalPrimitive` / `linearInChartSegment`);
3. the named hypotheses `ChartLocalPrimitiveSmoothExt` and
   `ChartLocalPrimitiveFTC` on each chart in the cover.

Discharging this admissibility predicate is the *single uniform
analytic content* needed to close the per-basis smoothness + FTC
hypotheses of item 14's reverse leg (`Topology/Item14From4MinimalInputs.lean`
chips `h_smooth_b`/`h_ftc_b`).

## What this file ships

* `PathPrimitiveAdmissibleChartCover om` — the bundled admissibility
  predicate.
* `pathPrimitive_contMDiff_of_admissible` — global `ContMDiff ω`.
* `pathPrimitive_eval_eq_mfderiv_of_admissible` — global FTC.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- **Admissibility predicate: chart cover + per-chart smoothness + FTC
named hypotheses.** At every point `x : X`, there is a chart `φ` with
convex target, a chart-basepoint `y ∈ φ.source`, and `x ∈ φ.source`,
such that the chart-local primitive's smoothness and FTC named
hypotheses hold. -/
def PathPrimitiveAdmissibleChartCover
    (om : HolomorphicOneForm X) : Prop :=
  ∀ x : X, ∃ (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X)
    (h_target_convex : Convex ℝ φ.target) (y : X) (hy : y ∈ φ.source),
    x ∈ φ.source ∧
      ChartLocalPrimitiveSmoothExt φ h_atlas h_target_convex y hy om ∧
      ChartLocalPrimitiveFTC φ h_atlas h_target_convex y hy om

/-- **Global `ContMDiff ω` of `pathPrimitive` under admissibility +
`LoopPeriodVanishes`.** -/
theorem pathPrimitive_contMDiff_of_admissible
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (h_admit : PathPrimitiveAdmissibleChartCover om) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (pathPrimitive h_conn x₀ om) := by
  intro x
  obtain ⟨φ, h_atlas, h_target_convex, y, hy, hx, h_smooth_ext, _⟩ :=
    h_admit x
  -- ContMDiffOn on φ.source from the local composition.
  have h_on :=
    pathPrimitive_contMDiffOn_source_of_ChartLocalPrimitiveSmoothExt
      h_conn x₀ om h_loop φ h_atlas h_target_convex y hy h_smooth_ext
  -- ContMDiffWithinAt at x ∈ φ.source.
  have h_within : ContMDiffWithinAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (pathPrimitive h_conn x₀ om) φ.source x :=
    h_on x hx
  -- Upgrade to ContMDiffAt via openness of φ.source.
  exact h_within.contMDiffAt (φ.open_source.mem_nhds hx)

/-- **Global FTC: `om.eval x = mfderiv pathPrimitive x`** under
admissibility + `LoopPeriodVanishes`. -/
theorem pathPrimitive_eval_eq_mfderiv_of_admissible
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (x₀ : X) (om : HolomorphicOneForm X)
    (h_loop : LoopPeriodVanishes om x₀)
    (h_admit : PathPrimitiveAdmissibleChartCover om)
    (x : X) :
    om.eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (pathPrimitive h_conn x₀ om) x := by
  obtain ⟨φ, h_atlas, h_target_convex, y, hy, hx, h_smooth_ext, h_ftc⟩ :=
    h_admit x
  exact mfderiv_pathPrimitive_eq_eval_on_source_of_ChartLocalPrimitiveFTC
    h_conn x₀ om h_loop φ h_atlas h_target_convex y hy h_smooth_ext h_ftc x hx

end JacobianChallenge

end
