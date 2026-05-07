/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphere
import JacobianChallenge.Topology.SurfaceGenus
import JacobianChallenge.Topology.SurfaceClassificationGenus

set_option diagnostics.threshold 100

/-! # The Riemann-sphere ↔ unit-2-sphere homeomorphism, packaged

This file packages a single small, honest consequence of
`RiemannSphere.toSphereHomeo : RiemannSphere ≃ₜ StandardS2`
(`JacobianChallenge/Manifold/RiemannSphere.lean:533`, itself a thin wrapper
around mathlib's `onePointEquivSphereOfFinrankEq`):

* the `TopologicalGenus` of the Riemann sphere coincides with that of the
  standard 2-sphere,

obtained by invoking the homeomorphism-invariance lemma
`Homeomorph.topologicalGenus_eq` from
`JacobianChallenge/Topology/SurfaceGenus.lean` on `toSphereHomeo`.

## Why this is just packaging, not a closure

This is **not** a discharge of `S2ImpliesGenus0` (challenge item 14, reverse
direction). At this mathlib pin:

* `JacobianChallenge.genus X = Module.finrank ℂ (HolomorphicOneForm X)`
  depends on the *complex* structure, not on the topology;
* `TopologicalGenus X = Module.finrank ℚ (H₁(X; ℚ))` depends only on the
  topology;
* there is no Hurewicz isomorphism, Mayer–Vietoris sequence, or CW
  computation in mathlib at the pin to evaluate `TopologicalGenus S² = 0`
  (see `SurfaceGenus.lean`, "Open challenge");
* there is no uniformization theorem in mathlib to identify a complex
  structure on `S²` with the standard one.

Both gaps are flagged in `S2ImpliesGenus0Discharge.lean` and
`SurfaceClassificationGenus.lean`. This file does *not* close them. It
contributes only the trivial topological-invariance bridge between the
two concrete spheres that show up in the challenge statement.

## What is honestly proven here

* `topologicalGenus_RiemannSphere_eq_topologicalGenus_StandardS2` — pure
  application of `Homeomorph.topologicalGenus_eq` to
  `RiemannSphere.toSphereHomeo`. **No `sorry`, no axiom.**
-/

universe u

namespace JacobianChallenge

/-- **Honest packaging.** The topological genus of the Riemann sphere
(`OnePoint ℂ`) equals the topological genus of the standard unit 2-sphere
in `ℝ³`.

Proof: `RiemannSphere.toSphereHomeo` exhibits a homeomorphism between
the two spaces, and `Homeomorph.topologicalGenus_eq` says
`TopologicalGenus` is a homeomorphism invariant. -/
theorem topologicalGenus_RiemannSphere_eq_topologicalGenus_StandardS2 :
    TopologicalGenus RiemannSphere = TopologicalGenus StandardS2 :=
  Homeomorph.topologicalGenus_eq RiemannSphere.toSphereHomeo

end JacobianChallenge
