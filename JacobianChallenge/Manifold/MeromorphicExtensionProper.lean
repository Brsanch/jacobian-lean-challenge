/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtensionContinuous
import Mathlib.Topology.Maps.Proper.Basic

set_option diagnostics.threshold 100

/-! # Properness and closedness of `f̃ : X → RiemannSphere`

This file records two basic topological properties of the pole extension
`f̃ := MeromorphicNonzero.toRiemannSphere f`:

* `MeromorphicNonzero.toRiemannSphere_isProperMap` — `f̃` is a **proper
  map** in the Bourbaki sense (`IsProperMap`).
* `MeromorphicNonzero.toRiemannSphere_isClosedMap` — `f̃` is a **closed
  map**.

Both follow immediately from the fact that `f̃` is continuous
(`toRiemannSphere_continuous`, ZZ3) together with the source being a
compact Hausdorff space:

* compact source + continuous ⇒ proper, via `Continuous.isProperMap`
  (the `[CompactSpace X]` overload of properness in Mathlib);
* compact source + Hausdorff target + continuous ⇒ closed, via
  `Continuous.isClosedMap` (which only needs `CompactSpace X` and
  `T2Space Y`).

These are foundational topological inputs for any future degree theory
on `f̃`: a proper map between manifolds has a well-defined
mapping degree, and being a closed map means images of closed sets are
closed (so e.g. the image of the pole locus is closed in `OnePoint ℂ`).
-/

open scoped Manifold Topology ContDiff

universe u

namespace JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **Properness of the pole extension.**

The map `f̃ := f.toRiemannSphere : X → RiemannSphere` is a proper map
(`IsProperMap`).

Proof: `toRiemannSphere_continuous` gives continuity, and any
continuous map out of a compact space is automatically proper (the
preimage of any compact set is closed in `X`, hence compact). -/
theorem toRiemannSphere_isProperMap (f : MeromorphicNonzero X) :
    IsProperMap f.toRiemannSphere :=
  f.toRiemannSphere_continuous.isProperMap

/-- **Closedness of the pole extension.**

The map `f̃ := f.toRiemannSphere : X → RiemannSphere` is a closed map:
the image of any closed subset of `X` is closed in `OnePoint ℂ`.

Proof: a continuous map from a compact space to a Hausdorff space is
automatically closed (closed subset of compact is compact, image of
compact under continuous is compact, compact in Hausdorff is closed).
Both `X` and `OnePoint ℂ` satisfy these hypotheses. -/
theorem toRiemannSphere_isClosedMap (f : MeromorphicNonzero X) :
    IsClosedMap f.toRiemannSphere :=
  f.toRiemannSphere_continuous.isClosedMap

end MeromorphicNonzero

end JacobianChallenge
