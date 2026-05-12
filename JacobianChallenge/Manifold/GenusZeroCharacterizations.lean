/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import JacobianChallenge.Manifold.HolomorphicOneFormEquivFromGenus

set_option diagnostics.threshold 100

/-! # Characterizations of `genus X = 0`

For any complex 1-manifold `X` modelled on `ℂ`, this file consolidates
the equivalences between several forms of "`X` has geometric genus
zero":

* `JacobianChallenge.genus X = 0` (the official definition).
* `Subsingleton (HolomorphicOneForm X)`.
* `∀ α : HolomorphicOneForm X, α = 0`.
* `HolomorphicOneFormEquivRiemannSphere X`.

All four are equivalent under
`[FiniteDimensional ℂ (HolomorphicOneForm X)]`. The first three were
already established in `HolomorphicOneFormLinear.lean`; this file adds
the fourth as an iff plus the cyclical chain.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

namespace JacobianChallenge

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Under finite-dimensionality, `genus X = 0` is equivalent to the
Riemann-sphere linear-equivalence hypothesis. -/
theorem genus_eq_zero_iff_holomorphicOneFormEquivRiemannSphere
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    JacobianChallenge.genus X = 0 ↔
      JacobianChallenge.HolomorphicOneFormEquivRiemannSphere X := by
  refine ⟨fun h => holomorphicOneFormEquivRiemannSphere_of_genus_zero X h, ?_⟩
  intro h
  obtain ⟨e⟩ := h
  haveI : Subsingleton (HolomorphicOneForm X) := by
    refine ⟨fun α β => ?_⟩
    have heq : e α = e β := Subsingleton.elim _ _
    exact e.injective heq
  exact genus_eq_zero_of_holomorphicOneForm_subsingleton X inferInstance

/-- Under finite-dimensionality, `Subsingleton (HolomorphicOneForm X)`
is equivalent to the Riemann-sphere linear-equivalence hypothesis. -/
theorem subsingleton_iff_holomorphicOneFormEquivRiemannSphere
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    Subsingleton (HolomorphicOneForm X) ↔
      JacobianChallenge.HolomorphicOneFormEquivRiemannSphere X := by
  refine ⟨fun h => holomorphicOneFormEquivRiemannSphere_of_subsingleton X, ?_⟩
  intro h
  obtain ⟨e⟩ := h
  refine ⟨fun α β => ?_⟩
  have heq : e α = e β := Subsingleton.elim _ _
  exact e.injective heq

/-- Under finite-dimensionality, `(∀ α, α = 0)` is equivalent to the
Riemann-sphere linear-equivalence hypothesis. -/
theorem forall_eq_zero_iff_holomorphicOneFormEquivRiemannSphere
    [FiniteDimensional ℂ (HolomorphicOneForm X)] :
    (∀ α : HolomorphicOneForm X, α = (0 : HolomorphicOneForm X)) ↔
      JacobianChallenge.HolomorphicOneFormEquivRiemannSphere X := by
  rw [← HolomorphicOneForm.subsingleton_iff_forall_eq_zero]
  exact subsingleton_iff_holomorphicOneFormEquivRiemannSphere X

/-! ## Without finite-dimensionality

Without `[FiniteDimensional ℂ (HolomorphicOneForm X)]`, we still have
the *one-way* implications:

* `Subsingleton → genus = 0` (since `finrank = 0` on subsingletons).
* `HolomorphicOneFormEquivRiemannSphere X → Subsingleton` (since the
  target is unconditionally subsingleton via zz274).

These compose to give `HolomorphicOneFormEquivRiemannSphere X →
genus X = 0` unconditionally — which is exactly zz275's
`genus_zero_of_linearEquiv_RiemannSphere_unconditional`.
-/

/-- Without finite-dim, `HolomorphicOneFormEquivRiemannSphere X` forces
`Subsingleton (HolomorphicOneForm X)`: the linear equivalence to a
subsingleton target makes the source a subsingleton too. -/
theorem subsingleton_of_holomorphicOneFormEquivRiemannSphere
    (h : JacobianChallenge.HolomorphicOneFormEquivRiemannSphere X) :
    Subsingleton (HolomorphicOneForm X) := by
  obtain ⟨e⟩ := h
  refine ⟨fun α β => ?_⟩
  have heq : e α = e β := Subsingleton.elim _ _
  exact e.injective heq

end JacobianChallenge
