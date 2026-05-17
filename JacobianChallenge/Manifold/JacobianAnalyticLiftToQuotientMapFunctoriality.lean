/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftComp
import JacobianChallenge.Manifold.PeriodLatticeLinearQuotientFunctoriality

set_option linter.unusedSectionVars false

/-! # Functoriality of `toQuotientMap` on per-curve lifts

For `JacobianAnalyticPushforwardLift` and `JacobianAnalyticPullbackLift`,
the `toQuotientMap` function commutes with the lift-level identity,
composition, and constant constructors. This file delivers the six
bridging identities by composing `quotientLinearMap_id` /
`quotientLinearMap_comp` / `quotientLinearMap_zero` (sister
`PeriodLatticeLinearQuotientFunctoriality.lean`) with the lift-level
constructors.

The identities exhibit the AnalyticJacobian-level pushforward /
pullback as functors at the *function* level (the smoothness-level
functoriality already lives in the `_contMDiff` lemmas).
-/

open scoped ContDiff Manifold
open Submodule

noncomputable section

namespace JacobianChallenge

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

namespace JacobianAnalyticPushforwardLift

variable {data_X : PeriodLatticeOfRankTwoG X}
  {data_Y : PeriodLatticeOfRankTwoG Y}
  {data_Z : PeriodLatticeOfRankTwoG Z}
  [DiscreteTopology data_X.lattice.toIntSubmodule]
  [IsZLattice ℝ data_X.lattice.toIntSubmodule]
  [DiscreteTopology data_Y.lattice.toIntSubmodule]
  [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
  [DiscreteTopology data_Z.lattice.toIntSubmodule]
  [IsZLattice ℝ data_Z.lattice.toIntSubmodule]

/-- **Identity functoriality at the pushforward `toQuotientMap` level.** -/
@[simp] theorem toQuotientMap_id' :
    (JacobianAnalyticPushforwardLift.id' data_X).toQuotientMap = id :=
  quotientLinearMap_id data_X.lattice.toIntSubmodule

/-- **Composition functoriality at the pushforward `toQuotientMap` level.** -/
theorem toQuotientMap_comp
    (liftYZ : JacobianAnalyticPushforwardLift data_Y data_Z)
    (liftXY : JacobianAnalyticPushforwardLift data_X data_Y) :
    (liftYZ.comp liftXY).toQuotientMap
      = liftYZ.toQuotientMap ∘ liftXY.toQuotientMap :=
  quotientLinearMap_comp data_X.lattice.toIntSubmodule
    data_Y.lattice.toIntSubmodule data_Z.lattice.toIntSubmodule
    liftXY.T liftYZ.T liftXY.lattice_match liftYZ.lattice_match

/-- **Constant-curve-map functoriality at the pushforward `toQuotientMap` level.**
The constant-curve pushforward sends every analytic-Jacobian class to `0`. -/
@[simp] theorem toQuotientMap_const (y₀ : Y) :
    (JacobianAnalyticPushforwardLift.const data_X data_Y y₀).toQuotientMap
      = fun _ => 0 :=
  quotientLinearMap_zero data_X.lattice.toIntSubmodule
    data_Y.lattice.toIntSubmodule

end JacobianAnalyticPushforwardLift

namespace JacobianAnalyticPullbackLift

variable {data_X : PeriodLatticeOfRankTwoG X}
  {data_Y : PeriodLatticeOfRankTwoG Y}
  {data_Z : PeriodLatticeOfRankTwoG Z}
  [DiscreteTopology data_X.lattice.toIntSubmodule]
  [IsZLattice ℝ data_X.lattice.toIntSubmodule]
  [DiscreteTopology data_Y.lattice.toIntSubmodule]
  [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
  [DiscreteTopology data_Z.lattice.toIntSubmodule]
  [IsZLattice ℝ data_Z.lattice.toIntSubmodule]

/-- **Identity functoriality at the pullback `toQuotientMap` level.** -/
@[simp] theorem toQuotientMap_id' :
    (JacobianAnalyticPullbackLift.id' data_X).toQuotientMap = id :=
  quotientLinearMap_id data_X.lattice.toIntSubmodule

/-- **Composition functoriality at the pullback `toQuotientMap` level.**
Contravariant: the `Z → Y → X` chain `liftXY.comp liftYZ` sends a pullback
along `g ∘ f` to first pulling back along `g`, then along `f`. -/
theorem toQuotientMap_comp
    (liftXY : JacobianAnalyticPullbackLift data_X data_Y)
    (liftYZ : JacobianAnalyticPullbackLift data_Y data_Z) :
    (liftXY.comp liftYZ).toQuotientMap
      = liftXY.toQuotientMap ∘ liftYZ.toQuotientMap :=
  quotientLinearMap_comp data_Z.lattice.toIntSubmodule
    data_Y.lattice.toIntSubmodule data_X.lattice.toIntSubmodule
    liftYZ.T liftXY.T liftYZ.lattice_match liftXY.lattice_match

/-- **Constant-curve-map functoriality at the pullback `toQuotientMap` level.**
The constant-curve pullback sends every analytic-Jacobian class to `0`. -/
@[simp] theorem toQuotientMap_const (y₀ : Y) :
    (JacobianAnalyticPullbackLift.const data_X data_Y y₀).toQuotientMap
      = fun _ => 0 :=
  quotientLinearMap_zero data_Y.lattice.toIntSubmodule
    data_X.lattice.toIntSubmodule

end JacobianAnalyticPullbackLift

end JacobianChallenge

end
