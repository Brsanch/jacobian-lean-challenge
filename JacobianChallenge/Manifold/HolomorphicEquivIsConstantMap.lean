/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.IsConstantMapAux

set_option diagnostics.threshold 100

/-! # `HolomorphicEquiv` ↔ `IsConstantMap` interaction

A biholomorphism is constant if and only if its codomain (equivalently
its domain) is a subsingleton. This is the natural compatibility
between `JacobianChallenge.IsConstantMap` (used by the degree
machinery) and `HolomorphicEquiv`.

* `HolomorphicEquiv.subsingleton_target_of_isConstantMap` —
  if `e` is constant, then `Subsingleton Y`.
* `HolomorphicEquiv.isConstantMap_of_subsingleton_target` —
  if `Y` is subsingleton and `X` is nonempty, then `e` is constant.
* `HolomorphicEquiv.subsingleton_iff` — `Subsingleton X ↔ Subsingleton Y`,
  via `Equiv.subsingleton_congr` on the underlying type equivalence.

(The iff version of "constant ↔ subsingleton target" requires
`[Nonempty X]` because `IsConstantMap` is `False` when the codomain is
empty, while `Subsingleton` is `True` vacuously.)

No `sorry`, no `axiom`. Pure API.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **One direction: a constant biholomorphism forces subsingleton
codomain (and source).** Unconditional — no nonemptyness needed. -/
theorem HolomorphicEquiv.subsingleton_target_of_isConstantMap
    (e : HolomorphicEquiv X Y)
    (h : JacobianChallenge.IsConstantMap (e : X → Y)) :
    Subsingleton Y := by
  obtain ⟨y₀, h_const⟩ := h
  refine ⟨fun y₁ y₂ => ?_⟩
  have h₁ : y₁ = y₀ := by
    have := h_const (e.toEquiv.symm y₁); simpa using this
  have h₂ : y₂ = y₀ := by
    have := h_const (e.toEquiv.symm y₂); simpa using this
  rw [h₁, h₂]

/-- **The other direction: a biholomorphism into a subsingleton with
inhabited domain is constant.** Requires `[Nonempty X]` to extract a
witness for the existential in `IsConstantMap`. -/
theorem HolomorphicEquiv.isConstantMap_of_subsingleton_target
    [hNE : Nonempty X] [hSub : Subsingleton Y]
    (e : HolomorphicEquiv X Y) :
    JacobianChallenge.IsConstantMap (e : X → Y) :=
  ⟨e hNE.some, fun _ => Subsingleton.elim _ _⟩

/-- **`Subsingleton` transports through a biholomorphism.** Mirrors
zz310's `subsingleton_holomorphicOneForm_iff` but on the base spaces,
not the 1-form spaces. -/
theorem HolomorphicEquiv.subsingleton_iff
    (e : HolomorphicEquiv X Y) :
    Subsingleton X ↔ Subsingleton Y :=
  e.toEquiv.subsingleton_congr

end JacobianChallenge

end
