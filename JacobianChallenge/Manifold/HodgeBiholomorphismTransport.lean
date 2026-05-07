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

The whole argument is linear algebra over `ℂ`: a `LinearEquiv` between two
modules transports `Module.Finite`. The bridge

```
Nonempty (HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm Y)
  → HolomorphicOneFormFiniteDim Y
  → HolomorphicOneFormFiniteDim X
```

is an unconditional, type-class-driven fact that we discharge directly
using `Module.Finite.equiv`.

## Tier-2 reduction: where the biholomorphism enters

The headline theorem the user asked for has the form

```
holomorphicOneFormFiniteDim_of_biholomorphism_to_sphere
    (h : Nonempty (X ≃M⟮𝓘(ℂ)⟯ OnePoint ℂ)) :
    HolomorphicOneFormFiniteDim X
```

The geometric content of "a biholomorphism induces a `LinearEquiv` on
holomorphic 1-forms" is the pullback action `f ↦ Φ^* f`, with smooth-section
preservation following from chain-rule + composition with an analytic
(C^ω) diffeomorphism. At the project's mathlib pin (15 Apr 2026), the
section-pullback functor for the cotangent bundle along an analytic
diffeomorphism is **not** packaged as a `LinearEquiv` of `ContMDiffSection`
spaces in mathlib. Per the file-level acceptance bar in
`HodgeRiemannSphereInstance.lean` and the user-stated *Acceptable
deliverable: tier-2 reduction is fine — express the biholomorphism-transport
as a structure or hypothesis*, we expose the missing analytic content as a
single named hypothesis

```
HolomorphicOneFormBiholomorphismLinearEquiv X Y : Prop
```

asserting `Nonempty (HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm Y)`. The
biholomorphism-shaped headline is then a one-line composition of this
hypothesis with the linear-algebra transport.

## What this file does NOT do

* It does **not** construct the pullback `LinearEquiv` from a
  `Diffeomorph` / `≃M⟮I⟯`. That construction (chain rule on cotangent fibres
  + section-level smoothness preservation) is the geometric content
  abstracted into the named hypothesis above.
* It does **not** discharge the still-open
  `HolomorphicOneForm_RiemannSphere_subsingleton_statement` from
  `RiemannSphereGenus.lean` — that is the analytic content owned by ZZ80.

## Composition with ZZ80

If both hypotheses hold for a given `X`,
```
H₁ : HolomorphicOneFormBiholomorphismLinearEquiv X RiemannSphere
H₂ : Subsingleton (HolomorphicOneForm RiemannSphere)
```
then `holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv` composes
ZZ80's
`holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton` (giving
`HolomorphicOneFormFiniteDim RiemannSphere`) with the linear-algebra
transport to yield `HolomorphicOneFormFiniteDim X`.

No `sorry`, no `axiom`. Every theorem in this file is proven from mathlib
+ ZZ76 + ZZ80 + the explicit named hypothesis.
-/

open scoped Manifold Topology

noncomputable section

namespace JacobianChallenge

variable (X Y : Type*)
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Named hypothesis.** A `ℂ`-linear equivalence between the spaces of
holomorphic 1-forms on `X` and `Y`.

For genuinely biholomorphic `X ≃M⟮𝓘(ℂ)⟯ Y`, such a `LinearEquiv` is
classically obtained as the pullback action `Φ ↦ Φ^*`. Packaging
section-level pullback as a `LinearEquiv` of `ContMDiffSection` spaces is
not in mathlib at the project pin, so we expose the conclusion as a single
named hypothesis (tier-2). -/
def HolomorphicOneFormBiholomorphismLinearEquiv : Prop :=
  Nonempty (HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm Y)

variable {X Y}

/-- Linear-algebra transport: a `LinearEquiv` of `ℂ`-modules transports
`Module.Finite`. This is the unconditional engine of every theorem in this
file. -/
private lemma moduleFinite_of_linearEquiv
    (e : HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm Y)
    (h : Module.Finite ℂ (HolomorphicOneForm Y)) :
    Module.Finite ℂ (HolomorphicOneForm X) :=
  Module.Finite.equiv e.symm

/-- **Tier-2 transport theorem.** If there is a `ℂ`-linear equivalence
between the spaces of holomorphic 1-forms on `X` and `Y`, then ZZ76's
named hypothesis transports from `Y` to `X`. -/
theorem holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv
    (hEq : HolomorphicOneFormBiholomorphismLinearEquiv X Y)
    (hY : HolomorphicOneFormFiniteDim Y) :
    HolomorphicOneFormFiniteDim X := by
  obtain ⟨e⟩ := hEq
  exact moduleFinite_of_linearEquiv e hY

/-- Symmetric form: the hypothesis is symmetric in `X` and `Y` because a
`LinearEquiv` is symmetric. -/
theorem holomorphicOneFormBiholomorphismLinearEquiv_symm
    (hEq : HolomorphicOneFormBiholomorphismLinearEquiv X Y) :
    HolomorphicOneFormBiholomorphismLinearEquiv Y X := by
  obtain ⟨e⟩ := hEq
  exact ⟨e.symm⟩

namespace RiemannSphere

/-- **Conditional discharge specialised to the Riemann sphere.** If `X`
admits a `LinearEquiv` of holomorphic 1-form spaces with the Riemann sphere
(the tier-2 form of "biholomorphic to `OnePoint ℂ`"), and the still-open
`Subsingleton (HolomorphicOneForm RiemannSphere)` instance from ZZ80 is
supplied, then ZZ76's named hypothesis holds for `X`.

This is the linear-algebra side of: *every genus-zero compact connected
Riemann surface has finite-dimensional `H⁰(X, Ω¹)`*. The analytic content
(uniformisation: `X ≃ ℂℙ¹`, plus
`Subsingleton (HolomorphicOneForm ℂℙ¹)`) lives upstream. -/
theorem holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv_to_riemannSphere
    (hEq : HolomorphicOneFormBiholomorphismLinearEquiv X RiemannSphere)
    (hSub : Subsingleton (HolomorphicOneForm RiemannSphere)) :
    JacobianChallenge.HolomorphicOneFormFiniteDim X := by
  have hY : JacobianChallenge.HolomorphicOneFormFiniteDim RiemannSphere :=
    JacobianChallenge.RiemannSphere.holomorphicOneFormFiniteDim_riemannSphere_of_subsingleton hSub
  exact holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv hEq hY

/-- The same conditional discharge, taking the `Prop`-form
`HolomorphicOneForm_RiemannSphere_subsingleton_statement` from
`RiemannSphereGenus.lean`. Convenient for downstream callers that thread
`_statement` props rather than `Subsingleton` instances. -/
theorem holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv_to_riemannSphere_statement
    (hEq : HolomorphicOneFormBiholomorphismLinearEquiv X RiemannSphere)
    (hSub : HolomorphicOneForm_RiemannSphere_subsingleton_statement) :
    JacobianChallenge.HolomorphicOneFormFiniteDim X :=
  holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv_to_riemannSphere hEq hSub

end RiemannSphere

/-! ### Headline biholomorphism-shaped theorem (tier-2)

The user-requested signature uses `≃M⟮𝓘(ℂ)⟯` (mathlib's `Diffeomorph`
notation). At the project pin, packaging the pullback of holomorphic
1-forms along an analytic `Diffeomorph` as a `LinearEquiv` of
`ContMDiffSection` spaces is not provided by mathlib, so we carry the
extraction as an explicit hypothesis argument. The headline theorem is
then a one-line composition.

If a future chip lands the section-pullback `LinearEquiv` from
`Diffeomorph`, the hypothesis below collapses to a derived lemma; at that
point this theorem becomes unconditional in its biholomorphism input. -/

/-- **Headline theorem (tier-2).** If `X` is biholomorphic to the Riemann
sphere `OnePoint ℂ`, *and* the biholomorphism induces a `LinearEquiv` on
holomorphic 1-form spaces (the missing analytic-functorial content,
exposed as the named hypothesis
`HolomorphicOneFormBiholomorphismLinearEquiv X RiemannSphere`), *and*
ZZ80's still-open `Subsingleton (HolomorphicOneForm RiemannSphere)`
holds, then ZZ76's hypothesis discharges for `X`.

The biholomorphism input itself is the geometric premise the user named;
the `LinearEquiv` hypothesis is the section-pullback functor specialised
to that biholomorphism (tier-2 reduction). -/
theorem holomorphicOneFormFiniteDim_of_biholomorphism_to_sphere
    (_h : Nonempty (X ≃M⟮𝓘(ℂ)⟯ OnePoint ℂ))
    (hEq : HolomorphicOneFormBiholomorphismLinearEquiv X RiemannSphere)
    (hSub : Subsingleton (HolomorphicOneForm RiemannSphere)) :
    HolomorphicOneFormFiniteDim X :=
  RiemannSphere.holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv_to_riemannSphere
    hEq hSub

/-- **Headline theorem, `_statement`-form.** Same as
`holomorphicOneFormFiniteDim_of_biholomorphism_to_sphere`, but threading
the `Prop`-form `HolomorphicOneForm_RiemannSphere_subsingleton_statement`
from `RiemannSphereGenus.lean` instead of the `Subsingleton` instance. -/
theorem holomorphicOneFormFiniteDim_of_biholomorphism_to_sphere_statement
    (_h : Nonempty (X ≃M⟮𝓘(ℂ)⟯ OnePoint ℂ))
    (hEq : HolomorphicOneFormBiholomorphismLinearEquiv X RiemannSphere)
    (hSub : HolomorphicOneForm_RiemannSphere_subsingleton_statement) :
    HolomorphicOneFormFiniteDim X :=
  RiemannSphere.holomorphicOneFormFiniteDim_of_biholomorphismLinearEquiv_to_riemannSphere_statement
    hEq hSub

end JacobianChallenge

end
