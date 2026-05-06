/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtension

set_option diagnostics.threshold 100

/-! # Continuity of `f̃ : X → RiemannSphere`

This file records the topological-degree input we need: the pole extension
`f̃ := MeromorphicNonzero.toRiemannSphere f` is a **continuous** map from
the compact Riemann surface `X` to the Riemann sphere `OnePoint ℂ`.

This is a direct corollary of the unconditional headline
`MeromorphicNonzero.toRiemannSphere_contMDiff` from `MeromorphicExtension`
(class `ω`/analytic), via `ContMDiff.continuous`.

It is the basic input to any topological-degree theory for `f̃`: a
continuous self-map of a compact orientable surface to the sphere has a
well-defined Brouwer degree.

## Main result

* `MeromorphicNonzero.toRiemannSphere_continuous` —
  `Continuous f.toRiemannSphere`.
-/

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **Continuity of the pole extension.**

The map `f̃ := f.toRiemannSphere : X → RiemannSphere` is continuous as a
map of topological spaces.

Proof: `toRiemannSphere_contMDiff` makes `f̃` `ContMDiff` of class `ω`
(analytic) from `X` to `RiemannSphere`. `ContMDiff` of any class implies
continuity (`ContMDiff.continuous`). -/
theorem toRiemannSphere_continuous (f : MeromorphicNonzero X) :
    Continuous f.toRiemannSphere :=
  f.toRiemannSphere_contMDiff.continuous

end MeromorphicNonzero
