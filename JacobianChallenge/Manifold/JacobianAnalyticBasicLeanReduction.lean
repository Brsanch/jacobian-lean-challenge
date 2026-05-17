/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticClosureBundle
import JacobianChallenge.Manifold.JacobianAnalyticPerCurveBundle

/-! # Basic.lean conditional reduction (E+F closure)

This file shows that, given the right pre-existing hypotheses
(C3-adjacent material + the E+F-cluster predicates landed this
session), OPEN.md's smoothness/injectivity items at the **analytic-
Jacobian level** all reduce to one-line discharges. The conditional
shape is

  (named hypotheses) ⟹ ContMDiff / Injective on AnalyticJacobian-level maps.

For the corresponding Basic.lean closures (e.g.
`Basic.lean.Jacobian.ofCurve_contMDiff`), the additional step is the
**C3 rewire** of `JacobianChallenge.Jacobian X` from `Pic⁰ X`
(currently) to `AnalyticJacobian X _ _` (the period-lattice quotient).
That rewire is C3-cluster work — when it lands, the bridge to
Basic.lean becomes one-line via `AddEquiv`-transport of the predicates
proven here.

## Headline reductions

* `analyticJacobian_ofCurve_contMDiff_of_bundle` — `ContMDiff` of
  `B.abelJacobiPoint` from a `JacobianAnalyticClosureBundle`. Item 17
  closure at the AnalyticJacobian level.
* `analyticJacobian_ofCurve_injective_of_bundle` — `Function.Injective`
  of `B.abelJacobiPoint` from a `JacobianAnalyticClosureBundle`
  (under `0 < genus X`). Item 16 closure at the AnalyticJacobian
  level.
* `analyticJacobian_pushforward_contMDiff_of_lift` — `ContMDiff` of
  `lift.toQuotientMap` from a `JacobianAnalyticPushforwardLift`. Item
  18 closure at the AnalyticJacobian level.
* `analyticJacobian_pullback_contMDiff_of_lift` — `ContMDiff` of
  `lift.toQuotientMap` from a `JacobianAnalyticPullbackLift`. Item
  21 closure at the AnalyticJacobian level.

Together with the LieAddGroup discharge (sister
`PeriodLatticeOfRankTwoG_LieGroupWiring.lean`) and the
chartedSpace/compactSpace discharges (sister `_Wiring`,
`_ComplexWiring`), this file completes the **E+F cluster at the
analytic-Jacobian level**. The remaining work for Basic.lean's
sorries is the C3 rewire + the discharge of the named hypotheses
listed above.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]

variable {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
  {h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α}

/-! ### Item 17 reduction -/

/-- **Item 17 at AnalyticJacobian level:** from a
`JacobianAnalyticClosureBundle`, the Abel-Jacobi map
`B.abelJacobiPoint : X → AnalyticJacobian _ α h` is `ContMDiff`. -/
theorem analyticJacobian_ofCurve_contMDiff_of_bundle
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    (bundle : JacobianAnalyticClosureBundle α h) :
    haveI := (PeriodLatticeOfRankTwoG.chartedSpaceHypothesis_holds
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h)).toChartedSpace
    ContMDiff (𝓘(ℂ, ℂ))
      (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
      (bundle.abel_jacobi_input.abelJacobiPoint :
        X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h) :=
  bundle.abel_jacobi_smoothness

/-! ### Item 16 reduction -/

/-- **Item 16 at AnalyticJacobian level:** from a
`JacobianAnalyticClosureBundle` and `0 < genus X`, the Abel-Jacobi map
is injective. -/
theorem analyticJacobian_ofCurve_injective_of_bundle
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofBundle
        (PeriodPairingData.ofSmoothCycle X) α h).lattice.toIntSubmodule]
    (bundle : JacobianAnalyticClosureBundle α h)
    (hpos : 0 < JacobianChallenge.genus X) :
    Function.Injective
      (bundle.abel_jacobi_input.abelJacobiPoint :
        X → AnalyticJacobian (PeriodPairingData.ofSmoothCycle X) α h) :=
  bundle.abel_jacobi_injective hpos

/-! ### Items 18 and 21 reductions -/

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

/-- **Item 18 at AnalyticJacobian level:** from a per-curve pushforward
lift, the induced map between AnalyticJacobians is `ContMDiff`. -/
theorem analyticJacobian_pushforward_contMDiff_of_lift
    {data_X : PeriodLatticeOfRankTwoG X}
    {data_Y : PeriodLatticeOfRankTwoG Y}
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (lift : JacobianAnalyticPushforwardLift data_X data_Y) :
    haveI : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
          (JacobianOfLattice X data_X) :=
      chartedSpace_quotient_of_zlattice data_X.lattice.toIntSubmodule
    haveI : ChartedSpace (Fin (JacobianChallenge.genus Y) → ℂ)
          (JacobianOfLattice Y data_Y) :=
      chartedSpace_quotient_of_zlattice data_Y.lattice.toIntSubmodule
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ)) ω
      lift.toQuotientMap :=
  lift.toQuotientMap_contMDiff

/-- **Item 21 at AnalyticJacobian level:** from a per-curve pullback
lift, the induced map between AnalyticJacobians is `ContMDiff`. -/
theorem analyticJacobian_pullback_contMDiff_of_lift
    {data_X : PeriodLatticeOfRankTwoG X}
    {data_Y : PeriodLatticeOfRankTwoG Y}
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (lift : JacobianAnalyticPullbackLift data_X data_Y) :
    haveI : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
          (JacobianOfLattice X data_X) :=
      chartedSpace_quotient_of_zlattice data_X.lattice.toIntSubmodule
    haveI : ChartedSpace (Fin (JacobianChallenge.genus Y) → ℂ)
          (JacobianOfLattice Y data_Y) :=
      chartedSpace_quotient_of_zlattice data_Y.lattice.toIntSubmodule
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
      lift.toQuotientMap :=
  lift.toQuotientMap_contMDiff

end JacobianChallenge

end
