/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPoint
import JacobianChallenge.Manifold.PeriodLatticeOfRankTwoG_LieGroupWiring

/-! # Named-hypothesis predicate for `abelJacobiPoint` smoothness (item 17)

The pointwise Abel-Jacobi map `B.abelJacobiPoint : X → AnalyticJacobian _ α h`
is the analytic-Jacobian-level version of `Jacobian.ofCurve`. Its
`ContMDiff` discharge is OPEN.md item 17's analytic-Jacobian-level
content.

Smoothness of `abelJacobiPoint` is the *fundamental theorem of calculus*
for path integrals on a Riemann surface:

  d/dQ (∫_{P₀}^{Q} ω) = ω(Q).

For this to be a Lean-level theorem we need either:

1. **Path-family smoothness** of `B.pathFromBase : Q ↦ (P₀ → Q)` viewed
   as a `ContMDiff` function `X → SmoothPath`, plus the chain rule for
   path-integration; OR
2. **Chart-cover lift** (C1 content of `CLOSURE_MAP.md`): a chart-cover
   of `X` on which `pathFromBase` is the straight-line-in-chart
   `Real.smoothTransition`-style path. Smoothness then follows because
   the integrand factors as a smooth function of the chart coordinate.

Both reductions are genuine analytic content; route 2 is the route
documented in `CLOSURE_MAP.md` §F.5 step 2 as the C1 chart-cover lift.

This file does not discharge that content. Instead it surfaces it as a
**named-hypothesis predicate** `AbelJacobiSmoothness B` that captures
the analytic-Jacobian-level smoothness of `Jacobian.ofCurve` at
basepoint `B.basePoint`. The actual content (path-integration smoothness)
is left as the named hypothesis.

The discharge of `AbelJacobiSmoothness B` is reduced to:

  ∃ chart cover + smooth-in-chart path family / FTC for path integrals.

Once C1 lands, this predicate becomes unconditional. The bridge from
this predicate to Basic.lean's `Jacobian.ofCurve_contMDiff` (item 17)
also requires the C3 rewire of `Jacobian X` to `AnalyticJacobian X _ _`.

## Net contribution

* `AbelJacobiSmoothness B` — named-hypothesis predicate carrying
  `ContMDiff` of `abelJacobiPoint B` at the analytic-Jacobian level.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-- **Named-hypothesis predicate** for OPEN.md item 17 at the analytic-
Jacobian level: `abelJacobiPoint B : X → AnalyticJacobian _ α h` is
`ContMDiff`.

The `[DiscreteTopology _]` and `[IsZLattice ℝ _]` instance arguments are
needed so the analytic-Jacobian target carries the complex-`ω` charted
space structure (via
`PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds`). The bundle
`h : PeriodLatticeDiscretenessBundle` supplies both via
`periodLatticeImage_discreteTopology_of_bundle` and
`periodLatticeImage_isZLattice_of_bundle`; callers can `haveI` those
two instances out of `h`.
-/
def AbelJacobiSmoothness
    (B : AbelJacobiInput α h)
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule] : Prop :=
  haveI := (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
    (PeriodLatticeOfRankTwoG.ofBundle
      (PeriodPairingData.ofSmoothCycle X) α h)).toChartedSpace
  ContMDiff (𝓘(ℂ, ℂ))
    (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
    (B.abelJacobiPoint :
      X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h)

end JacobianChallenge

end
