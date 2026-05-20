/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CanonicalPushforwardPullbackLift

set_option linter.unusedSectionVars false

/-! # `ContMDiff` of canonical pushforward / pullback on canonical analytic Jacobians

Specializes the `toQuotientMap_contMDiff` theorems of
`JacobianAnalyticPushforwardLift` / `.PullbackLift` to the canonical
lattices exposed by `[HasJacobianAnalyticStructure X]`.

The headline corollaries:

* `canonicalPushforward_contMDiff` — for X, Y with the class + a
  pushforward lift, the induced map
  `CanonicalAnalyticJacobianAnonymous X → CanonicalAnalyticJacobianAnonymous Y`
  is `ContMDiff`.

* `canonicalPullback_contMDiff` — same in the reverse direction.

These are the C3-rewire-ready analogues of `Basic.lean`'s items 18 and
21 at the analytic Jacobian level: given the substantive lattice-match
certificate (the per-curve analytic input), the smooth map between the
canonical analytic Jacobians is automatic.

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

/-- **`ContMDiff` of the canonical pushforward map.** Given the
canonical period lattices on X and Y + a per-curve pushforward lift,
the induced map between `CanonicalAnalyticJacobianAnonymous`-types is
ω-smooth.

This is the analytic-Jacobian-target analogue of
`Jacobian.pushforward_contMDiff` (item 18 of `Basic.lean`). -/
theorem canonicalPushforward_contMDiff
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
    haveI : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
          (JacobianOfLattice X (canonicalPeriodLatticeOfRankTwoG
            (canonicalBasisFromAnalyticStructure X))) :=
      chartedSpace_quotient_of_zlattice
        (canonicalPeriodLatticeOfRankTwoG
          (canonicalBasisFromAnalyticStructure X)).lattice.toIntSubmodule
    haveI : ChartedSpace (Fin (JacobianChallenge.genus Y) → ℂ)
          (JacobianOfLattice Y (canonicalPeriodLatticeOfRankTwoG
            (canonicalBasisFromAnalyticStructure Y))) :=
      chartedSpace_quotient_of_zlattice
        (canonicalPeriodLatticeOfRankTwoG
          (canonicalBasisFromAnalyticStructure Y)).lattice.toIntSubmodule
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ)) ω
      (canonicalPushforwardLift f hf lattice_match).toQuotientMap :=
  JacobianAnalyticPushforwardLift.toQuotientMap_contMDiff
    (canonicalPushforwardLift f hf lattice_match)

/-- **`ContMDiff` of the canonical pullback map.** Given the canonical
period lattices on X and Y + a per-curve pullback lift, the induced map
between `CanonicalAnalyticJacobianAnonymous`-types is ω-smooth.

This is the analytic-Jacobian-target analogue of
`Jacobian.pullback_contMDiff` (item 21 of `Basic.lean`). -/
theorem canonicalPullback_contMDiff
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
    haveI : ChartedSpace (Fin (JacobianChallenge.genus X) → ℂ)
          (JacobianOfLattice X (canonicalPeriodLatticeOfRankTwoG
            (canonicalBasisFromAnalyticStructure X))) :=
      chartedSpace_quotient_of_zlattice
        (canonicalPeriodLatticeOfRankTwoG
          (canonicalBasisFromAnalyticStructure X)).lattice.toIntSubmodule
    haveI : ChartedSpace (Fin (JacobianChallenge.genus Y) → ℂ)
          (JacobianOfLattice Y (canonicalPeriodLatticeOfRankTwoG
            (canonicalBasisFromAnalyticStructure Y))) :=
      chartedSpace_quotient_of_zlattice
        (canonicalPeriodLatticeOfRankTwoG
          (canonicalBasisFromAnalyticStructure Y)).lattice.toIntSubmodule
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ)) ω
      (canonicalPullbackLift f hf T lattice_match).toQuotientMap :=
  JacobianAnalyticPullbackLift.toQuotientMap_contMDiff
    (canonicalPullbackLift f hf T lattice_match)

end JacobianChallenge

end
