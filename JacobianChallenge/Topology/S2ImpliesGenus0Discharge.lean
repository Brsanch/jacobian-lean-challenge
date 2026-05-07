/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.RiemannSphereGenus
import Mathlib.LinearAlgebra.Dimension.Finite

set_option diagnostics.threshold 100

/-! # Discharge of `S2ImpliesGenus0` via a holomorphic-1-forms equivalence

This file discharges the named hypothesis
`JacobianChallenge.S2ImpliesGenus0 X` from
`JacobianChallenge/Topology/SurfaceClassificationGenus.lean`
(challenge item 14, reverse direction) under a single explicit
intermediate hypothesis: a `ℂ`-linear equivalence

```
HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm RiemannSphere
```

together with the genus-zero statement for the Riemann sphere
(`RiemannSphere.genus_RiemannSphere_statement`).

## Why an intermediate hypothesis is necessary

`JacobianChallenge.genus X` is defined as
`Module.finrank ℂ (HolomorphicOneForm X)`, which depends on the
**complex-manifold** structure on `X`, not on its underlying topology.
A bare homeomorphism `X ≃ₜ S²` carries *no* information about
`HolomorphicOneForm X`, so there is no purely topological route from
`Nonempty (X ≃ₜ StandardS2)` to `genus X = 0` at this mathlib pin.

The classical mathematical content closing the gap is the **uniformization
theorem**: any complex structure on `S²` is biholomorphic to the standard
Riemann sphere `OnePoint ℂ`. A biholomorphism induces a `ℂ`-linear
equivalence of holomorphic-1-form spaces (pullback). That equivalence —
the `ℂ`-linear-equivalence layer — is what we take as the explicit
hypothesis in this file.

So the reduction performed here is:

```
   uniformization ───────► biholomorphism X ≅ RiemannSphere
                                │
                                ▼ (pullback of 1-forms)
            HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm RiemannSphere
                                │
                                ▼ (this file)
                            genus X = 0
```

We close the bottom arrow honestly. The top two arrows (uniformization
and pullback-of-1-forms) are not in mathlib at the pinned commit and are
not attempted here.

## What is honestly proven here

* `genus_eq_of_holomorphicOneForm_linearEquiv` — given a `ℂ`-linear
  equivalence between `HolomorphicOneForm X` and `HolomorphicOneForm Y`
  (for `X`, `Y` two complex manifolds modelled on `ℂ`), their geometric
  genera are equal. **No `sorry`, no axiom.** Uses
  `LinearEquiv.finrank_eq`.

* `genus_zero_of_linearEquiv_RiemannSphere` — given the same equivalence
  with `Y = RiemannSphere` and the open statement
  `RiemannSphere.genus_RiemannSphere_statement`, conclude
  `genus X = 0`.

* `s2ImpliesGenus0_of_linearEquiv` — discharges
  `S2ImpliesGenus0 X` from the same two inputs (the homeomorphism is
  ignored, as it carries no holomorphic data).

## What is left as an open hypothesis

* `HolomorphicOneFormEquivRiemannSphere X : Prop` — there exists a
  `ℂ`-linear equivalence `HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm
  RiemannSphere`. Classically, this follows from uniformization +
  pullback-of-1-forms; not in mathlib at the pinned commit.

The reduction in this file converts the **two** open inputs

```
  HolomorphicOneFormEquivRiemannSphere X
  RiemannSphere.genus_RiemannSphere_statement
```

into the **one** open output `S2ImpliesGenus0 X`. So the chip moves the
open frontier from "topological-S² → genus 0" to "linear-equivalence of
holomorphic-1-form spaces", which is strictly closer to the analytic
content that classical proofs use.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

/-! ### Linear-equivalence transfer of genus -/

/-- **Honest content.** A `ℂ`-linear equivalence between the spaces of
holomorphic 1-forms of two complex manifolds `X` and `Y` (both modelled on
`ℂ`) implies their geometric genera coincide.

Proof: `JacobianChallenge.genus` is `Module.finrank ℂ (HolomorphicOneForm
·)`, and `LinearEquiv.finrank_eq` says a linear equivalence preserves
`finrank`. -/
theorem genus_eq_of_holomorphicOneForm_linearEquiv
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (e : HolomorphicOneForm X ≃ₗ[ℂ] HolomorphicOneForm Y) :
    JacobianChallenge.genus X = JacobianChallenge.genus Y := by
  unfold JacobianChallenge.genus
  exact e.finrank_eq

/-- Specialisation of `genus_eq_of_holomorphicOneForm_linearEquiv` to the
Riemann sphere: combined with the open statement
`genus RiemannSphere = 0`, a linear equivalence of holomorphic-1-form
spaces forces `genus X = 0`. -/
theorem genus_zero_of_linearEquiv_RiemannSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (e : HolomorphicOneForm X ≃ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere)
    (hRS : RiemannSphere.genus_RiemannSphere_statement) :
    JacobianChallenge.genus X = 0 := by
  -- `genus X = genus RiemannSphere` by the linear equivalence.
  have hEq : JacobianChallenge.genus X
      = JacobianChallenge.genus JacobianChallenge.RiemannSphere :=
    genus_eq_of_holomorphicOneForm_linearEquiv e
  -- And `genus RiemannSphere = 0` is exactly the open statement.
  rw [hEq]
  exact hRS

/-! ### Named open hypothesis, packaged

The reduction goes through a single explicit hypothesis: that
`HolomorphicOneForm X` and `HolomorphicOneForm RiemannSphere` are
`ℂ`-linearly equivalent. We package this as a `Prop`-valued definition,
mirroring the style of `Genus0ImpliesS2 / S2ImpliesGenus0` in the sister
file. -/

/-- **Open hypothesis.** A `ℂ`-linear equivalence between the space of
holomorphic 1-forms on `X` and on the Riemann sphere.

Classically this is supplied by uniformization (any complex structure on
`S²` is biholomorphic to the standard Riemann sphere) followed by
pullback of 1-forms along the biholomorphism. Neither uniformization nor
the pullback-of-1-forms construction is in mathlib at the pinned commit.

Stated as `Nonempty` so it is `Prop`-valued, matching the convention of
the sister file. -/
def HolomorphicOneFormEquivRiemannSphere
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop :=
  Nonempty (HolomorphicOneForm X ≃ₗ[ℂ]
            HolomorphicOneForm JacobianChallenge.RiemannSphere)

/-! ### Discharge of `S2ImpliesGenus0` -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Discharge of `S2ImpliesGenus0`** under a single explicit
intermediate hypothesis.

Given:

* `hEq : HolomorphicOneFormEquivRiemannSphere X` — a `ℂ`-linear
  equivalence between the holomorphic-1-form spaces of `X` and the
  Riemann sphere;
* `hRS : RiemannSphere.genus_RiemannSphere_statement` — the open
  statement that `genus RiemannSphere = 0`;

the reverse-direction implication
`S2ImpliesGenus0 X = (Nonempty (X ≃ₜ StandardS2) → genus X = 0)`
holds. **No `sorry`, no axiom.**

Note: the homeomorphism `X ≃ₜ StandardS2` is *unused* in the proof,
because at this mathlib pin a topological homeomorphism carries no
holomorphic data. The mathematical work transferring "topological
sphere" to "biholomorphism with Riemann sphere" lives entirely inside
`HolomorphicOneFormEquivRiemannSphere X` (which is supplied externally,
by uniformization + pullback). -/
theorem s2ImpliesGenus0_of_linearEquiv
    (hEq : HolomorphicOneFormEquivRiemannSphere X)
    (hRS : RiemannSphere.genus_RiemannSphere_statement) :
    S2ImpliesGenus0 X := by
  intro _hHomeo
  obtain ⟨e⟩ := hEq
  exact genus_zero_of_linearEquiv_RiemannSphere e hRS

/-- Specialisation of `s2ImpliesGenus0_of_linearEquiv` taking the linear
equivalence directly (rather than wrapped in `Nonempty`). -/
theorem s2ImpliesGenus0_of_linearEquiv'
    (e : HolomorphicOneForm X ≃ₗ[ℂ]
          HolomorphicOneForm JacobianChallenge.RiemannSphere)
    (hRS : RiemannSphere.genus_RiemannSphere_statement) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_of_linearEquiv ⟨e⟩ hRS

end JacobianChallenge
