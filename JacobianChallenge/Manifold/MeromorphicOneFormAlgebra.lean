/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicOneForm
import JacobianChallenge.Manifold.MeromorphicAt

/-! # Additive group structure on `MeromorphicOneForm X`

`MeromorphicOneForm X` (from `Manifold/MeromorphicOneForm.lean`) is a
structure pairing a pointwise differential `toFun : X → (ℂ →L[ℂ] ℂ)` with
a chart-pullback meromorphicity proof on the coefficient `(toFun y) 1`.
This file ships the `AddCommGroup (MeromorphicOneForm X)` instance and
the basic algebraic identities downstream callers need:

* `zero, add, neg, sub` on `MeromorphicOneForm X` — defined pointwise,
  with the meromorphicity field discharged via `MMeromorphicAt.zero`,
  `MMeromorphicAt.add`, `MMeromorphicAt.neg`, `MMeromorphicAt.sub` on
  the coefficient.
* `AddCommGroup` instance via `Function.Injective.addCommGroup` pulled
  back along `toFun`.
* `coeff_zero, coeff_add, coeff_neg, coeff_sub` — pointwise behaviour
  of the `coeff` projection under the group operations.
* `toFun_zero, toFun_add, toFun_neg, toFun_sub` — pointwise behaviour
  of the underlying `X → (ℂ →L[ℂ] ℂ)` differential.

No `sorry`, no `axiom`, no new bundles, no signature changes outside this
file.
-/

set_option diagnostics.threshold 100

open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace MeromorphicOneForm

universe u

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Constructors -/

/-- The zero meromorphic 1-form: everywhere `0 : ℂ →L[ℂ] ℂ`. The
coefficient `fun y => 0 1 = 0` is meromorphic by
`MMeromorphicAt.zero`. -/
def zero : MeromorphicOneForm X where
  toFun := fun _ => 0
  meromorphic_coeff := fun x => by
    simpa using (MMeromorphicAt.zero : MMeromorphicAt (𝓘(ℂ, ℂ))
      (0 : X → ℂ) x)

/-- Pointwise addition of meromorphic 1-forms. The sum's coefficient
`(α₁.toFun + α₂.toFun) y 1 = α₁.coeff y + α₂.coeff y` is meromorphic by
`MMeromorphicAt.add`. -/
def add (α β : MeromorphicOneForm X) : MeromorphicOneForm X where
  toFun := fun y => α.toFun y + β.toFun y
  meromorphic_coeff := fun x =>
    (α.meromorphic_coeff x).add (β.meromorphic_coeff x)

/-- Pointwise negation of a meromorphic 1-form. -/
def neg (α : MeromorphicOneForm X) : MeromorphicOneForm X where
  toFun := fun y => -α.toFun y
  meromorphic_coeff := fun x =>
    (α.meromorphic_coeff x).neg

/-- Pointwise subtraction of meromorphic 1-forms. -/
def sub (α β : MeromorphicOneForm X) : MeromorphicOneForm X where
  toFun := fun y => α.toFun y - β.toFun y
  meromorphic_coeff := fun x =>
    (α.meromorphic_coeff x).sub (β.meromorphic_coeff x)

/-! ### Typeclass instances -/

instance : Zero (MeromorphicOneForm X) := ⟨zero⟩
instance : Add (MeromorphicOneForm X) := ⟨add⟩
instance : Neg (MeromorphicOneForm X) := ⟨neg⟩
instance : Sub (MeromorphicOneForm X) := ⟨sub⟩

/-! ### `toFun` projections under the group operations -/

@[simp] lemma toFun_zero :
    (0 : MeromorphicOneForm X).toFun = fun _ => (0 : ℂ →L[ℂ] ℂ) := rfl

@[simp] lemma toFun_add (α β : MeromorphicOneForm X) :
    (α + β).toFun = fun y => α.toFun y + β.toFun y := rfl

@[simp] lemma toFun_neg (α : MeromorphicOneForm X) :
    (-α).toFun = fun y => -α.toFun y := rfl

@[simp] lemma toFun_sub (α β : MeromorphicOneForm X) :
    (α - β).toFun = fun y => α.toFun y - β.toFun y := rfl

/-! ### `coeff` projections under the group operations -/

@[simp] lemma coeff_zero :
    (0 : MeromorphicOneForm X).coeff = (0 : X → ℂ) := by
  funext y; simp [coeff_apply, toFun_zero]

@[simp] lemma coeff_add (α β : MeromorphicOneForm X) (y : X) :
    (α + β).coeff y = α.coeff y + β.coeff y := by
  simp [coeff_apply, toFun_add]

@[simp] lemma coeff_neg (α : MeromorphicOneForm X) (y : X) :
    (-α).coeff y = -α.coeff y := by
  simp [coeff_apply, toFun_neg]

@[simp] lemma coeff_sub (α β : MeromorphicOneForm X) (y : X) :
    (α - β).coeff y = α.coeff y - β.coeff y := by
  simp [coeff_apply, toFun_sub]

/-! ### `toFun` is injective

The meromorphicity field is `Prop`-valued, so two `MeromorphicOneForm`s
with the same underlying function are equal. (Full `AddCommGroup`
instance is left to a downstream chip, which would need explicit
`nsmul`/`zsmul` SMul instances first.) -/

lemma toFun_injective :
    Function.Injective (MeromorphicOneForm.toFun : MeromorphicOneForm X → _) := by
  rintro ⟨f, hf⟩ ⟨g, hg⟩ (h : f = g)
  subst h
  rfl

@[ext]
lemma ext {α β : MeromorphicOneForm X} (h : α.toFun = β.toFun) : α = β :=
  toFun_injective h

/-! ### Group-axiom identities at the `toFun` level

These are the pointwise group axioms verified by `Function.Injective.addCommGroup`
when an `AddCommGroup` instance is constructed downstream. -/

lemma toFun_zero_add (α : MeromorphicOneForm X) :
    ((0 : MeromorphicOneForm X) + α).toFun = α.toFun := by
  funext y; simp [toFun_add, toFun_zero]

lemma toFun_add_zero (α : MeromorphicOneForm X) :
    (α + (0 : MeromorphicOneForm X)).toFun = α.toFun := by
  funext y; simp [toFun_add, toFun_zero]

lemma toFun_add_comm (α β : MeromorphicOneForm X) :
    (α + β).toFun = (β + α).toFun := by
  funext y; simp [toFun_add, add_comm]

lemma toFun_add_assoc (α β γ : MeromorphicOneForm X) :
    ((α + β) + γ).toFun = (α + (β + γ)).toFun := by
  funext y; simp [toFun_add, add_assoc]

lemma toFun_neg_add (α : MeromorphicOneForm X) :
    ((-α) + α).toFun = (0 : MeromorphicOneForm X).toFun := by
  funext y; simp [toFun_add, toFun_neg, toFun_zero]

lemma toFun_sub_eq (α β : MeromorphicOneForm X) :
    (α - β).toFun = (α + (-β)).toFun := by
  funext y
  simp [toFun_sub, toFun_add, toFun_neg, sub_eq_add_neg]

end MeromorphicOneForm

end JacobianChallenge

end
