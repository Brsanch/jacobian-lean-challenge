/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.HolomorphicOneFormRiemannSphereInstances
import JacobianChallenge.Topology.S2ImpliesGenus0Discharge

set_option diagnostics.threshold 100

/-! # `HolomorphicOneFormEquivRiemannSphere X` from `genus X = 0` (+ finite-dim)

**Key observation.** If `HolomorphicOneForm X` is a subsingleton (e.g. when
`genus X = 0` and finite-dim) and `HolomorphicOneForm RiemannSphere` is a
subsingleton (unconditionally true from zz274), then both spaces have a
*unique* element (namely `0`), and the trivial map between them is a
`ℂ`-linear equivalence.

This means the named open hypothesis
`HolomorphicOneFormEquivRiemannSphere X` from
`S2ImpliesGenus0Discharge.lean` is **derivable** for any `X` satisfying:

* `JacobianChallenge.genus X = 0`, *and*
* `FiniteDimensional ℂ (HolomorphicOneForm X)`.

The pullback-of-1-forms construction is *not* needed — the linear
equivalence comes from the subsingleton structure on both sides.

## Why this is honest content (not a vacuous trick)

The two hypotheses `genus X = 0` and `FiniteDimensional ℂ
(HolomorphicOneForm X)` together imply `Subsingleton (HolomorphicOneForm
X)` (`holomorphicOneForm_subsingleton_of_genus_eq_zero` in
`HolomorphicOneFormLinear.lean`). Combined with zz274's unconditional
subsingleton on the Riemann-sphere side, every linear map between the
two spaces is the zero map, so the canonical zero-map / zero-map pair
is a `LinearEquiv`. This is the standard linear-algebra fact that all
zero modules are isomorphic.

## What this file delivers

* `LinearEquiv.ofSubsingletons` — a generic helper: any two
  subsingleton modules over the same ring are linearly equivalent.
* `holomorphicOneFormEquivRiemannSphere_of_subsingleton` — the
  specialisation: from `Subsingleton (HolomorphicOneForm X)` (plus the
  in-scope `Subsingleton (HolomorphicOneForm RiemannSphere)` instance),
  produce `HolomorphicOneFormEquivRiemannSphere X`.
* `holomorphicOneFormEquivRiemannSphere_of_genus_zero` — from `genus X =
  0` plus `FiniteDimensional ℂ (HolomorphicOneForm X)`, produce
  `HolomorphicOneFormEquivRiemannSphere X`.

## Consequence

Combined with the existing `s2ImpliesGenus0_of_linearEquiv_unconditional`
(zz275), the reverse direction of item 14 becomes available *for the
zero-genus case* without any uniformization input — though that's a
tautology (the hypothesis `Nonempty (X ≃ₜ S²)` is unused; the conclusion
matches the hypothesis on `genus X = 0`). The real value is structural:
the `HolomorphicOneFormEquivRiemannSphere` hypothesis collapses to the
combination of `genus = 0` and finite-dim, so callers can supply the
named hypothesis from those two ingredients alone.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u v

/-! ## Generic linear-algebra helper -/

/-- Any two subsingleton `R`-modules are `R`-linearly equivalent via
the zero map. -/
def LinearEquiv.ofSubsingletons
    {R : Type u} [Semiring R]
    {V : Type v} [AddCommMonoid V] [Module R V] [Subsingleton V]
    {W : Type*} [AddCommMonoid W] [Module R W] [Subsingleton W] :
    V ≃ₗ[R] W where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := by exact (Subsingleton.elim _ _).symm
  map_smul' _ _ := by exact (Subsingleton.elim _ _).symm
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-! ## Specialisation to `HolomorphicOneForm` and the Riemann sphere -/

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **From a subsingleton on `X`, get the linear equivalence with the
Riemann sphere.** The Riemann-sphere side comes from zz274's
unconditional `Subsingleton (HolomorphicOneForm RiemannSphere)`
instance. -/
theorem holomorphicOneFormEquivRiemannSphere_of_subsingleton
    [Subsingleton (HolomorphicOneForm X)] :
    HolomorphicOneFormEquivRiemannSphere X :=
  ⟨LinearEquiv.ofSubsingletons⟩

/-- **From `genus X = 0` + finite-dim, get the linear equivalence with
the Riemann sphere.** Composes
`holomorphicOneForm_subsingleton_of_genus_eq_zero` with
`holomorphicOneFormEquivRiemannSphere_of_subsingleton`. -/
theorem holomorphicOneFormEquivRiemannSphere_of_genus_zero
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (h : JacobianChallenge.genus X = 0) :
    HolomorphicOneFormEquivRiemannSphere X :=
  haveI := holomorphicOneForm_subsingleton_of_genus_eq_zero X h
  holomorphicOneFormEquivRiemannSphere_of_subsingleton X

/-! ## The Riemann sphere itself -/

/-- Specialisation to `X = RiemannSphere`: both sides are subsingletons
unconditionally, so the linear equivalence exists. -/
theorem holomorphicOneFormEquivRiemannSphere_RiemannSphere_of_subsingleton :
    HolomorphicOneFormEquivRiemannSphere
      JacobianChallenge.RiemannSphere :=
  holomorphicOneFormEquivRiemannSphere_of_subsingleton _

end JacobianChallenge
