/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPerCurveBundle

set_option linter.unusedSectionVars false

/-! # Identity functoriality for `JacobianAnalyticPushforwardLift`

For the identity map `id : X → X` (same data on both sides), the
pushforward lift carries `T := ContinuousLinearMap.id`, automatically
matching `data.lattice` with itself.

The resulting `toQuotientMap` is the identity map on
`JacobianOfLattice X data`, and its `ContMDiff`-conclusion is the
trivial `contMDiff_id` (via `toQuotientMap_contMDiff` ⇒
`analyticJacobian_linearLift_contMDiff` ⇒ `quotientLinearMap_contMDiff`
on the identity linear map).

This is the cleanest functoriality witness for the AnalyticJacobian-
level pushforward at the identity curve map. Pullback dual lives in
`JacobianAnalyticPullbackLiftId.lean` (sister chip).
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The identity-curve-map pushforward lift. -/
noncomputable def JacobianAnalyticPushforwardLift.id'
    (data : PeriodLatticeOfRankTwoG X)
    [DiscreteTopology data.lattice.toIntSubmodule]
    [IsZLattice ℝ data.lattice.toIntSubmodule] :
    JacobianAnalyticPushforwardLift data data where
  f := _root_.id
  contMDiff_f := contMDiff_id
  T := ContinuousLinearMap.id ℂ (Fin (JacobianChallenge.genus X) → ℂ)
  lattice_match := fun _ hx => hx

/-- The identity-curve-map pullback lift. -/
noncomputable def JacobianAnalyticPullbackLift.id'
    (data : PeriodLatticeOfRankTwoG X)
    [DiscreteTopology data.lattice.toIntSubmodule]
    [IsZLattice ℝ data.lattice.toIntSubmodule] :
    JacobianAnalyticPullbackLift data data where
  f := _root_.id
  contMDiff_f := contMDiff_id
  T := ContinuousLinearMap.id ℂ (Fin (JacobianChallenge.genus X) → ℂ)
  lattice_match := fun _ hx => hx

/-! ### Constant-curve-map case -/

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

/-- The constant-curve-map pushforward lift: for `f : X → Y` constant
at `y₀`, the analytic-Jacobian-level pushforward is the zero map. -/
noncomputable def JacobianAnalyticPushforwardLift.const
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (y₀ : Y) :
    JacobianAnalyticPushforwardLift data_X data_Y where
  f := fun _ => y₀
  contMDiff_f := contMDiff_const
  T := 0
  lattice_match := fun _ _ => Submodule.zero_mem _

/-- The constant-curve-map pullback lift: for `f : X → Y` constant at
`y₀`, the analytic-Jacobian-level pullback is the zero map. -/
noncomputable def JacobianAnalyticPullbackLift.const
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (y₀ : Y) :
    JacobianAnalyticPullbackLift data_X data_Y where
  f := fun _ => y₀
  contMDiff_f := contMDiff_const
  T := 0
  lattice_match := fun _ _ => Submodule.zero_mem _

end JacobianChallenge

end
