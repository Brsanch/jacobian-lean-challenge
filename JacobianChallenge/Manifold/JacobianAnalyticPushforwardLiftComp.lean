/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftOfCurve
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftId

set_option linter.unusedSectionVars false

/-! # Composition of per-curve pushforward / pullback lifts

For composable curve maps `f : X → Y` and `g : Y → Z`, two
`JacobianAnalyticPushforwardLift`s with matching middle data compose to
give a `JacobianAnalyticPushforwardLift data_X data_Z` for `g ∘ f`.

The composed lift carries:
* `f := g ∘ f` (function composition).
* `T := liftYZ.T.comp liftXY.T` (composition of the two CLM lifts).
* `lattice_match` derived from the two factor lattice-matches.

Together with `JacobianAnalyticPushforwardLift.id'` (sister
`JacobianAnalyticPushforwardLiftId.lean`), this exhibits the
analytic-Jacobian-level pushforward as a **covariant functor** on the
category of (smooth curve maps between compact connected complex
1-manifolds with chosen period bundles).

The pullback case mirrors with directions swapped (contravariant
functor).
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- **Composition of pushforward lifts.** -/
noncomputable def JacobianAnalyticPushforwardLift.comp
    {data_X : PeriodLatticeOfRankTwoG X}
    {data_Y : PeriodLatticeOfRankTwoG Y}
    {data_Z : PeriodLatticeOfRankTwoG Z}
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    [DiscreteTopology data_Z.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Z.lattice.toIntSubmodule]
    (liftYZ : JacobianAnalyticPushforwardLift data_Y data_Z)
    (liftXY : JacobianAnalyticPushforwardLift data_X data_Y) :
    JacobianAnalyticPushforwardLift data_X data_Z where
  f := liftYZ.f ∘ liftXY.f
  contMDiff_f := liftYZ.contMDiff_f.comp liftXY.contMDiff_f
  T := liftYZ.T.comp liftXY.T
  lattice_match := by
    intro x hx
    -- (liftYZ.T.comp liftXY.T) x = liftYZ.T (liftXY.T x).
    -- liftXY.T x ∈ data_Y.lattice (by liftXY.lattice_match).
    -- liftYZ.T (...) ∈ data_Z.lattice (by liftYZ.lattice_match).
    have h1 : liftXY.T x ∈ data_Y.lattice.toIntSubmodule :=
      liftXY.lattice_match x hx
    have h2 : liftYZ.T (liftXY.T x) ∈ data_Z.lattice.toIntSubmodule :=
      liftYZ.lattice_match _ h1
    exact h2

/-- **Composition of pullback lifts.** Note the contravariant direction:
the pullback lift for `g : Y → Z` and the pullback lift for `f : X → Y`
compose to a pullback lift for `g ∘ f : X → Z`. The middle lattice
data must align. -/
noncomputable def JacobianAnalyticPullbackLift.comp
    {data_X : PeriodLatticeOfRankTwoG X}
    {data_Y : PeriodLatticeOfRankTwoG Y}
    {data_Z : PeriodLatticeOfRankTwoG Z}
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    [DiscreteTopology data_Z.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Z.lattice.toIntSubmodule]
    (liftXY : JacobianAnalyticPullbackLift data_X data_Y)
    (liftYZ : JacobianAnalyticPullbackLift data_Y data_Z) :
    JacobianAnalyticPullbackLift data_X data_Z where
  f := liftYZ.f ∘ liftXY.f
  contMDiff_f := liftYZ.contMDiff_f.comp liftXY.contMDiff_f
  -- For pullback direction: T : ℂ^{gZ} →L[ℂ] ℂ^{gX} = liftXY.T ∘ liftYZ.T
  -- (since liftXY.T : ℂ^{gY} → ℂ^{gX} and liftYZ.T : ℂ^{gZ} → ℂ^{gY}).
  T := liftXY.T.comp liftYZ.T
  lattice_match := by
    intro x hx
    have h1 : liftYZ.T x ∈ data_Y.lattice.toIntSubmodule :=
      liftYZ.lattice_match x hx
    have h2 : liftXY.T (liftYZ.T x) ∈ data_X.lattice.toIntSubmodule :=
      liftXY.lattice_match _ h1
    exact h2

end JacobianChallenge

end
