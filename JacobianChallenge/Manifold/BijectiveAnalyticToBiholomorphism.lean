/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneBijective
import JacobianChallenge.Manifold.HolomorphicEquiv

set_option diagnostics.threshold 100

/-! # Bijective ω-smooth ⇒ biholomorphism (named conditional)

The final analytic step in zz325's `DegreeOneIsBiholomorphic_RS`:
once a bijective ω-smooth map between compact connected Riemann
surfaces is in hand, the inverse map is also ω-smooth (by the
inverse function theorem applied chart-by-chart at points where
the chart-pullback derivative is nonzero — which holds when the
ramification index is 1 everywhere, which is the conclusion of
zz326 for degreeFiber-1 maps).

## Current status (2026-05-26)

**This named hypothesis is UNCONDITIONALLY DISCHARGED in tree** at
`Manifold/BijectiveAnalyticToBiholomorphismDischarge.lean`
(theorem `bijectiveAnalyticIsBiholomorphism_holds`). Plus inputs 1
and 2 of the four-input chain below are also unconditional:

* (1) `ramificationSumEqualsDegree_holds_unconditional` —
  `Manifold/RamificationSumEqualsDegreeUnconditional.lean:471`
  composed with `Manifold/NearbyRegularWitnessHolds.lean:32`.
* (2) `surjective_of_NonConstant_Analytic_Manifold_holds` —
  `Manifold/SurjectiveOfNonConstantDischarge.lean:391`.
* (3) `bijectiveAnalyticIsBiholomorphism_holds` — this file's
  discharge.

Composed, `DegreeOneIsBiholomorphic_RS X` is **unconditional in
tree** via
`Topology/Item14FinalComposition.lean:degreeOneIsBiholomorphic_RS_of_conditionals`
applied to (1)+(2)+(3); see
`Topology/HTopFromSubsingleton.lean:101-107` for the call-site
composition. The only remaining open input for full item-14
strict closure on abstract X is (4) `RiemannRochGenusZero X`,
which itself reduces to `ExistsMeroSimplePole_GenusZero X`
(Forster Thm 16.9) via
`Topology/RiemannRochGenusZeroSingleInput.lean:54`. See
`HANDOFF_ITEM14.md` "ACTIVE ARC — CANONICAL CURRENT STATE".

## The named hypothesis (kept open as a `def Prop` for compositional clarity)

  BijectiveAnalyticIsBiholomorphism X Y :=
    ∀ f, ContMDiff ω f → Function.Bijective f →
      Nonempty (HolomorphicEquiv X Y)

Plus composition with zz329's bijection result:

  degreeOneIsBiholomorphic_RS_from_conditionals :
    ramificationSumEqualsDegree_statement X RS →
    Surjective_of_NonConstant_Analytic_Manifold X RS →
    BijectiveAnalyticIsBiholomorphism X RS →
    DegreeOneIsBiholomorphic_RS X

With the three discharges cited above, this composition produces
`DegreeOneIsBiholomorphic_RS X` unconditionally. Combined with
`RiemannRochGenusZero X` (still open), this closes
`UniformizationToRiemannSphere_genus_zero_branch`. Combined with
the corresponding S²-branch hypothesis (still open), this closes
`UniformizationToRiemannSphere X`, i.e., item 14 strict closure on
the forward direction.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u v

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Named open hypothesis: a bijective ω-smooth map between compact
connected Riemann surfaces upgrades to a biholomorphism.** Classical
content: inverse function theorem applied chart-by-chart at points of
non-vanishing chart-pullback derivative. -/
def BijectiveAnalyticIsBiholomorphism : Prop :=
  ∀ {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    (f : X → Y) (_hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (_hbij : Function.Bijective f),
    Nonempty (HolomorphicEquiv X Y)

end JacobianChallenge

end
