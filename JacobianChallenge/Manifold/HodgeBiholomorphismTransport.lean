/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HodgeFiniteDimensional
import JacobianChallenge.Manifold.HodgeRiemannSphereInstance
import JacobianChallenge.Manifold.RiemannSphere

/-! # Biholomorphism transport for `HolomorphicOneFormFiniteDim`

This file provides a **conditional discharge** of ZZ76's named hypothesis
`JacobianChallenge.HolomorphicOneFormFiniteDim X` for any complex 1-manifold
`X` that is biholomorphic to the Riemann sphere `OnePoint ℂ`. Composed with
ZZ80's `holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton` bridge,
this lets the still-open `Subsingleton (HolomorphicOneForm RiemannSphere)`
input from `RiemannSphereGenus.lean` propagate to *any* genus-zero surface
in the project's typeclass setting.

## What is honestly proven here (no `sorry`, no `axiom`)

The whole argument is `Prop`-level transport: a hypothesis encoding the
implication

```
HolomorphicOneFormFiniteDim Y → HolomorphicOneFormFiniteDim X
```

composes with ZZ80's sphere bridge to give
`HolomorphicOneFormFiniteDim X` for any `X` admitting such a transport
from the Riemann sphere.

## Tier-2 reduction: where the biholomorphism enters

Classically, a biholomorphism `Φ : X ≃ Y` induces a `ℂ`-linear isomorphism
`Φ^* : HolomorphicOneForm Y → HolomorphicOneForm X` (the pullback of
1-forms; smoothness preservation is the chain rule, holomorphicity of the
pullback follows from holomorphicity of `Φ`). This in turn transports
`Module.Finite` and hence ZZ76's hypothesis.

At the project's mathlib pin (15 Apr 2026), the section-level pullback
functor for the cotangent bundle along an analytic diffeomorphism is **not**
packaged in mathlib, and the `≃M⟮I⟯` (`Diffeomorph`) notation requested in
the original chip prompt is not available at this pin either. Per the
user-stated *Acceptable deliverable: tier-2 reduction is fine — express the
biholomorphism-transport as a structure or hypothesis*, we expose the
missing analytic content as a single named `Prop` hypothesis

```
HolomorphicOneFormFiniteDimTransport X Y : Prop
  := HolomorphicOneFormFiniteDim Y → HolomorphicOneFormFiniteDim X
```

asserting that finite-dimensionality transports from `Y` to `X`. This is
the strongest tier-2 reduction one can take: it is the literal conclusion
the biholomorphism's pullback action would yield, exposed as a hypothesis.

## What this file does NOT do

* It does **not** construct the pullback transport from a biholomorphism.
  That construction (chain rule on cotangent fibres + section-level
  smoothness preservation) is the geometric content abstracted into the
  named hypothesis above.
* It does **not** discharge the still-open
  `HolomorphicOneForm_RiemannSphere_subsingleton_statement` from
  `RiemannSphereGenus.lean` — that is the analytic content owned by ZZ80.

## Composition with ZZ80

If both hypotheses hold for a given `X`,
```
H₁ : HolomorphicOneFormFiniteDimTransport X RiemannSphere
H₂ : Subsingleton (HolomorphicOneForm RiemannSphere)
```
then `holomorphicOneFormFiniteDim_of_transport_from_riemannSphere` composes
ZZ80's `holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton` (giving
`HolomorphicOneFormFiniteDim RiemannSphere`) with the transport hypothesis
to yield `HolomorphicOneFormFiniteDim X`.

No `sorry`, no `axiom`. Every theorem in this file is proven from mathlib
+ ZZ76 + ZZ80 + the explicit named hypothesis.
-/

open scoped Manifold Topology

noncomputable section

namespace JacobianChallenge

variable (X Y : Type*)
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ⊤ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y] [IsManifold 𝓘(ℂ) ⊤ Y]

/-- **Named tier-2 hypothesis.** Finite-dimensionality of holomorphic
1-forms transports from `Y` to `X`.

For genuinely biholomorphic `X` and `Y` this is the conclusion of the
classical pullback action `Φ^* : HolomorphicOneForm Y → HolomorphicOneForm X`
applied to the named ZZ76 hypothesis (a `LinearEquiv` would transport
`Module.Finite` directly via `Module.Finite.equiv`). Packaging the
section-level pullback is not in mathlib at the project pin, so we expose
the conclusion itself as a named hypothesis. -/
def HolomorphicOneFormFiniteDimTransport : Prop :=
  HolomorphicOneFormFiniteDim Y → HolomorphicOneFormFiniteDim X

variable {X Y}

/-- **Tier-2 transport theorem.** If finite-dimensionality of holomorphic
1-forms transports from `Y` to `X`, then ZZ76's named hypothesis
transports from `Y` to `X`. This is the trivial application of the
hypothesis itself; it is recorded under a stable name so downstream files
can cite it without unfolding the `Prop`-level definition. -/
theorem holomorphicOneFormFiniteDim_of_transport
    (hT : HolomorphicOneFormFiniteDimTransport X Y)
    (hY : HolomorphicOneFormFiniteDim Y) :
    HolomorphicOneFormFiniteDim X :=
  hT hY

end JacobianChallenge

/-! ### Sphere-specialised conditional discharges

These compose the abstract transport with ZZ80's sphere bridge. -/

namespace JacobianChallenge

namespace RiemannSphere

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- **Conditional discharge specialised to the Riemann sphere.** If `X`
admits a finite-dimensionality transport from the Riemann sphere (the
tier-2 form of "biholomorphic to `OnePoint ℂ`"), and the still-open
`Subsingleton (HolomorphicOneForm RiemannSphere)` instance from ZZ80 is
supplied, then ZZ76's named hypothesis holds for `X`.

This is the linear-algebra side of: *every genus-zero compact connected
Riemann surface has finite-dimensional `H⁰(X, Ω¹)`*. The analytic content
(uniformisation: `X ≃ ℂℙ¹`, plus
`Subsingleton (HolomorphicOneForm ℂℙ¹)`) lives upstream. -/
theorem holomorphicOneFormFiniteDim_of_transport_from_riemannSphere
    (hT : HolomorphicOneFormFiniteDimTransport X RiemannSphere)
    (hSub : Subsingleton (HolomorphicOneForm RiemannSphere)) :
    JacobianChallenge.HolomorphicOneFormFiniteDim X := by
  have hY : JacobianChallenge.HolomorphicOneFormFiniteDim RiemannSphere :=
    JacobianChallenge.RiemannSphere.holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton hSub
  exact hT hY

/-- The same conditional discharge, taking the `Prop`-form
`HolomorphicOneForm_RiemannSphere_subsingleton_statement` from
`RiemannSphereGenus.lean`. Convenient for downstream callers that thread
`_statement` props rather than `Subsingleton` instances. -/
theorem holomorphicOneFormFiniteDim_of_transport_from_riemannSphere_statement
    (hT : HolomorphicOneFormFiniteDimTransport X RiemannSphere)
    (hSub : HolomorphicOneForm_RiemannSphere_subsingleton_statement) :
    JacobianChallenge.HolomorphicOneFormFiniteDim X :=
  holomorphicOneFormFiniteDim_of_transport_from_riemannSphere hT hSub

end RiemannSphere

end JacobianChallenge

end
