/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveContMDiff
import JacobianChallenge.Manifold.JacobianAnalyticOfCurveInjective
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardPullbackContMDiff

/-! # E+F closure: composite named-hypothesis bundle for items 16/17/18/21

This file bundles the E+F-cluster named hypotheses on the analytic
Jacobian into a single structure `JacobianAnalyticClosureBundle X α h`
so that downstream callers (notably the `Basic.lean` instance-wiring
layer, once `Jacobian X` is rewired to `AnalyticJacobian X _ _` by C3)
can supply a single bundle to flip OPEN.md items 16, 17, 18, 21
simultaneously.

## Bundle fields

* `abel_jacobi_input : AbelJacobiInput α h` — smooth-path-connectedness
  witness (existing in tree).
* `abel_jacobi_smoothness : AbelJacobiSmoothness abel_jacobi_input`
  (item 17 content) — `ContMDiff` of the pointwise Abel-Jacobi map.
  *Discharge route:* C1 chart-cover lift (`CLOSURE_MAP.md` §F.5 step 2)
  + FTC for path integrals.
* `abel_jacobi_injective : AbelJacobiInjective abel_jacobi_input` (item
  16 content) — `Function.Injective` of the pointwise Abel-Jacobi map
  when `0 < genus X`. *Discharge route:* Abel's theorem on compact
  Riemann surfaces (`CLOSURE_MAP.md` §F.5 step 3, C4 content).
* `pushforward_lift, pullback_lift` — for items 18, 21, downstream
  callers supply the ℂ-linear cover lifts on a per-curve-map basis;
  `analyticJacobian_linearLift_contMDiff` then gives `ContMDiff` on
  the analytic-Jacobian-level pushforward/pullback. These are
  per-`f : X → Y`-hypotheses, so they live in a sister
  `JacobianAnalyticPerCurveBundle` (not in this file).

## Items 4, 5, 10, 11, 12, 13 (instances on `Jacobian X`)

These are NOT bundled here because they require the C3 rewire of
`Jacobian X` to `AnalyticJacobian X _ _` (so the typeclasses fire on
the right target type). Once C3 rewires:

* Item 4 (`TopologicalSpace`) is `JacobianOfLattice.instTopologicalSpace`
  via the rewire.
* Item 5 (`ChartedSpace`) is `chartedSpaceHypothesis_holds.toChartedSpace`.
* Item 10 (`T2Space`) is `JacobianOfLattice.instT2Space`.
* Item 11 (`CompactSpace`) is
  `PeriodLatticeOfRankTwoG.compactSpaceHypothesis_holds`.
* Item 12 (`IsManifold`) is `chartedSpaceHypothesis_holds.toIsManifold`.
* Item 13 (`LieAddGroup`) is
  `PeriodLatticeOfRankTwoG.lieAddGroupHypothesis_holds` (this
  session's deliverable, sister file
  `PeriodLatticeOfRankTwoG_LieGroupWiring.lean`).

## Anti-hack

The bundle's fields are about an *honest* analytic Jacobian; the trivial
hack `Λ = ⊥` is rejected at the bundle level via
`PeriodLatticeDiscretenessBundle h`'s rank-`2g` and discreteness
content. Items 16/17 are non-trivial under `0 < genus X`; at `genus = 0`
the AnalyticJacobian is trivial (and items 16/17 are vacuous).
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **E+F closure bundle**: aggregates the named-hypothesis predicates
for OPEN.md items 16 and 17 at the analytic-Jacobian level. -/
structure JacobianAnalyticClosureBundle (α : Basis (Fin (JacobianChallenge.genus X)) ℂ
        (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule] where
  /-- Smooth-path-connectedness witness. -/
  abel_jacobi_input : AbelJacobiInput α h
  /-- Item 17 predicate: `abelJacobiPoint` is `ContMDiff`. -/
  abel_jacobi_smoothness : AbelJacobiSmoothness abel_jacobi_input
  /-- Item 16 predicate: `abelJacobiPoint` is injective when `0 < genus X`. -/
  abel_jacobi_injective : AbelJacobiInjective abel_jacobi_input

end JacobianChallenge

end
