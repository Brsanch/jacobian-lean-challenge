/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructure
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftOfCurve

set_option linter.unusedSectionVars false

/-! # Canonical pushforward / pullback lifts on `CanonicalAnalyticJacobianAnonymous`

For X, Y with `[HasJacobianAnalyticStructure X]` and
`[HasJacobianAnalyticStructure Y]`, this file specialises
`JacobianAnalyticPushforwardLift.ofCurveMap` /
`JacobianAnalyticPullbackLift.ofCurveMap` to the canonical
`PeriodLatticeOfRankTwoG` data of each.

The result: given a curve map `f : X → Y` (ω-smooth) and a per-direction
linear lift + lattice-match certificate, produce a
`JacobianAnalyticPushforwardLift` (resp. `.PullbackLift`) for the
canonical lattices, whose `toQuotientMap` then provides a `ContMDiff`
map between the canonical analytic Jacobians.

This is the C3-rewire-ready form of items 18 and 21 at the analytic
Jacobian level: given the per-curve data + lattice-match certificate
(both substantive analytic content), the smooth pushforward / pullback
map between canonical analytic Jacobians follows.

## What this file ships

* `canonicalPushforwardLift` — `JacobianAnalyticPushforwardLift` over
  canonical lattices.
* `canonicalPullbackLift` — `JacobianAnalyticPullbackLift` over
  canonical lattices.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Canonical pushforward lift.** Given the canonical period-lattice
data on X and Y via the basis-anonymous class, plus a curve map +
linear lift + lattice-match certificate, produce the per-curve
pushforward bundle. -/
noncomputable def canonicalPushforwardLift
    [HasJacobianAnalyticStructure X]
    [HasJacobianAnalyticStructure Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (lattice_match :
      ∀ x ∈ (canonicalPeriodLatticeOfRankTwoG
              (canonicalBasisFromAnalyticStructure X)).lattice.toIntSubmodule,
        HolomorphicOneForm.pushforwardLinearLift
          (canonicalBasisFromAnalyticStructure X)
          (canonicalBasisFromAnalyticStructure Y) f hf x
          ∈ (canonicalPeriodLatticeOfRankTwoG
              (canonicalBasisFromAnalyticStructure Y)).lattice.toIntSubmodule) :
    JacobianAnalyticPushforwardLift
      (canonicalPeriodLatticeOfRankTwoG
        (canonicalBasisFromAnalyticStructure X))
      (canonicalPeriodLatticeOfRankTwoG
        (canonicalBasisFromAnalyticStructure Y)) :=
  JacobianAnalyticPushforwardLift.ofCurveMap _ _
    (canonicalBasisFromAnalyticStructure X)
    (canonicalBasisFromAnalyticStructure Y) f hf lattice_match

/-- **Canonical pullback lift.** Given the canonical period-lattice
data on X and Y, plus a curve map + pullback linear lift + lattice-match
certificate (lattice on Y goes into lattice on X), produce the per-curve
pullback bundle. -/
noncomputable def canonicalPullbackLift
    [HasJacobianAnalyticStructure X]
    [HasJacobianAnalyticStructure Y]
    (f : X → Y) (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (T : (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
          (Fin (JacobianChallenge.genus X) → ℂ))
    (lattice_match :
      ∀ x ∈ (canonicalPeriodLatticeOfRankTwoG
              (canonicalBasisFromAnalyticStructure Y)).lattice.toIntSubmodule,
        T x ∈ (canonicalPeriodLatticeOfRankTwoG
                (canonicalBasisFromAnalyticStructure X)).lattice.toIntSubmodule) :
    JacobianAnalyticPullbackLift
      (canonicalPeriodLatticeOfRankTwoG
        (canonicalBasisFromAnalyticStructure X))
      (canonicalPeriodLatticeOfRankTwoG
        (canonicalBasisFromAnalyticStructure Y)) :=
  JacobianAnalyticPullbackLift.ofCurveMap _ _ f hf T lattice_match

end JacobianChallenge

end
