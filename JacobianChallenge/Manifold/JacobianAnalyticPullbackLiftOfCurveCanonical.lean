/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftOfCurve
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackLinearLift

set_option linter.unusedSectionVars false

/-! # Canonical-`T` variant of `JacobianAnalyticPullbackLift.ofCurveMap`

The existing `JacobianAnalyticPullbackLift.ofCurveMap` takes the
pullback CLM `T : (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ)` as an *explicit*
argument so downstream callers can choose any equivalent form. This
chip ships the **canonical** variant which fixes `T` to the
`pullbackLinearLift` (i.e., `Matrix.mulVecLin (pullbackMatrix αX αY f hf)`).

Sister to `JacobianAnalyticPushforwardLift.ofCurveMap` whose
`T := pushforwardLinearLift αX αY f hf` is already canonical (no
caller choice). With this chip, both sides of the pushforward/pullback
pair have a canonical-`T` per-curve constructor.

Built on top of: the new `pullbackLinearLift` primitive
(`HolomorphicOneFormPullbackLinearLift.lean`) and the generic
`ofCurveMap`.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Canonical-`T` pullback lift constructor.** Specialisation of
`JacobianAnalyticPullbackLift.ofCurveMap` with `T` fixed to the
`pullbackLinearLift` of the basis matrix. -/
noncomputable def JacobianAnalyticPullbackLift.ofCurveMapCanonical
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (lattice_match : ∀ w ∈ data_Y.lattice.toIntSubmodule,
      HolomorphicOneForm.pullbackLinearLift αX αY f hf w
        ∈ data_X.lattice.toIntSubmodule) :
    JacobianAnalyticPullbackLift data_X data_Y :=
  JacobianAnalyticPullbackLift.ofCurveMap data_X data_Y f hf
    (HolomorphicOneForm.pullbackLinearLift αX αY f hf) lattice_match

@[simp] theorem JacobianAnalyticPullbackLift.ofCurveMapCanonical_T
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (lattice_match : ∀ w ∈ data_Y.lattice.toIntSubmodule,
      HolomorphicOneForm.pullbackLinearLift αX αY f hf w
        ∈ data_X.lattice.toIntSubmodule) :
    (JacobianAnalyticPullbackLift.ofCurveMapCanonical
        data_X data_Y αX αY f hf lattice_match).T
      = HolomorphicOneForm.pullbackLinearLift αX αY f hf := rfl

@[simp] theorem JacobianAnalyticPullbackLift.ofCurveMapCanonical_f
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (lattice_match : ∀ w ∈ data_Y.lattice.toIntSubmodule,
      HolomorphicOneForm.pullbackLinearLift αX αY f hf w
        ∈ data_X.lattice.toIntSubmodule) :
    (JacobianAnalyticPullbackLift.ofCurveMapCanonical
        data_X data_Y αX αY f hf lattice_match).f
      = f := rfl

end JacobianChallenge

end
