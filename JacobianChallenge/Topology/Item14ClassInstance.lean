/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromSingleUniformization
import JacobianChallenge.Manifold.PullbackLinearEquiv

set_option diagnostics.threshold 100

/-! # Typeclass version of `UniformizationToRiemannSphere`

zz309 ships `UniformizationToRiemannSphere X` as a `Prop`-valued
hypothesis. This file packages the same predicate as a `class` so it
can be resolved by Lean's instance search:

  class FactUniformizationToRiemannSphere (X : Type*) ... : Prop where
    out : UniformizationToRiemannSphere X

Plus instance discharges:

* `instFact_RiemannSphere` — the trivial discharge for
  `X = RiemannSphere` (identity biholomorphism).
* `instFact_of_HolomorphicEquiv_RiemannSphere` — given an arbitrary
  `e : HolomorphicEquiv X RiemannSphere` (as a `Nonempty` instance),
  discharge the predicate by feeding `e` through both disjuncts.

With these, item-14 biconditional resolves by instance search whenever
the caller knows X is biholomorphic to RS.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

/-- **Typeclass form of `UniformizationToRiemannSphere`.** Wraps the
zz309 predicate so it can be resolved via instance search. -/
class FactUniformizationToRiemannSphere (X : Type*)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop where
  out : UniformizationToRiemannSphere X

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Item 14 from the typeclass.** When the typeclass is in scope, the
biconditional `genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)` holds by
instance resolution + zz309's assembly. -/
theorem genus_eq_zero_iff_homeo_of_fact
    [FactUniformizationToRiemannSphere X] :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_of_uniformizationToRiemannSphere
    FactUniformizationToRiemannSphere.out

/-! ## Instance discharges -/

/-- **Trivial discharge for the Riemann sphere.** -/
instance instFactUniformizationToRiemannSphere_RiemannSphere :
    FactUniformizationToRiemannSphere JacobianChallenge.RiemannSphere where
  out := JacobianChallenge.RiemannSphere.uniformizationToRiemannSphere_RiemannSphere

/-- **Discharge from a known biholomorphism with `RiemannSphere`.**
Given `[Nonempty (HolomorphicEquiv X RiemannSphere)]` in instance scope,
the predicate is dischargeable via zz308's
`uniformizationGenus0_of_HolomorphicEquiv` and zz307's
`isHolomorphicOneFormPullback_for_all_symm_of_HolomorphicEquiv`, or
more directly by feeding the witness through either disjunct.
-/
instance instFactUniformizationToRiemannSphere_of_HolomorphicEquiv
    [hE : Nonempty (HolomorphicEquiv X JacobianChallenge.RiemannSphere)] :
    FactUniformizationToRiemannSphere X where
  out := fun _ => hE

end JacobianChallenge

end
