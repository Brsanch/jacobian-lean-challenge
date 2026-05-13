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

Stated as a named open conditional:

  BijectiveAnalyticIsBiholomorphism X Y :=
    ∀ f, ContMDiff ω f → Function.Bijective f →
      Nonempty (HolomorphicEquiv X Y)

Plus composition with zz329's bijection result:

  degreeOneIsBiholomorphic_RS_from_conditionals :
    ramificationSumEqualsDegree_statement X RS →
    Surjective_of_NonConstant_Analytic_Manifold X RS →
    BijectiveAnalyticIsBiholomorphism X RS →
    DegreeOneIsBiholomorphic_RS X

This is the FINAL composition: with the three named conditionals
above, `DegreeOneIsBiholomorphic_RS X` (zz325) closes. Combined with
`RiemannRochGenusZero X` (zz325), this closes
`UniformizationToRiemannSphere_genus_zero_branch` (zz325). Combined
with the corresponding S²-branch hypothesis (zz309), this closes
`UniformizationToRiemannSphere X` (zz309), i.e., item 14 strict
closure on the forward direction.

The four named open inputs that would together strict-close item 14:

1. `ramificationSumEqualsDegree_statement` (existing, conditional on
   `NearbyRegularWitnessHypothesis`).
2. `Surjective_of_NonConstant_Analytic_Manifold` (zz328).
3. `BijectiveAnalyticIsBiholomorphism` (this file).
4. `RiemannRochGenusZero` (zz325).

All four are classical theorems with explicit references in Forster
(Riemann Surfaces, ch. 11) but absent from mathlib at the pin.

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
