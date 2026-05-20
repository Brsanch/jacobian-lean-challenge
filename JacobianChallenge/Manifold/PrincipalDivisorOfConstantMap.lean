/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroConstantBridge
import JacobianChallenge.Manifold.MeromorphicAtAlgebra
import JacobianChallenge.Divisor.OrderFunSign

set_option linter.unusedSectionVars false

/-! # `principalDivisorMap f = 0` from `IsConstantMap f.toRiemannSphere`

When `f : MeromorphicNonzero X` has constant `f.toRiemannSphere`, the
bridge `isConstantMap_toFun_of_isConstantMap_toRiemannSphere` gives
`IsConstantMap f.toFun` with value `w : ℂ`. The
`MeromorphicNonzero.nonvanishing_germ` field forces `w ≠ 0` (the
`mmeromorphicOrderAt (const 0) x = ⊤` collapse is precisely what the
non-vanishing-germ hypothesis rules out). Then
`orderFun_const_ne_zero` gives `orderFun f.toFun x = 0` pointwise,
and `principalDivisorMap_apply` lifts to
`principalDivisorMap f = 0` as a `Finsupp`.

## What ships

* `MeromorphicNonzero.toFun_const_value_ne_zero` — for any constant-value
  bridge `f.toFun ≡ w`, `w ≠ 0` (via `nonvanishing_germ`).

* `MeromorphicNonzero.principalDivisorMap_eq_zero_of_isConstantMap` —
  the universal bridge `IsConstantMap f.toRiemannSphere
    → principalDivisorMap f = 0`.

This discharges the `h_constant_divisor_zero` input of
`abelGeneratorPeriodCondition_of_period_and_constant_divisor_zero`,
collapsing it to a tautology. -/

noncomputable section

open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Constant value of `f.toFun` is non-zero.** If `f.toFun ≡ w`,
then `w ≠ 0`. Reason: the `nonvanishing_germ` field of
`MeromorphicNonzero` says
`mmeromorphicOrderAt (𝓘(ℂ,ℂ)) f.toFun x ≠ ⊤` at every `x`; for the
constant zero function this fails (`mmeromorphicOrderAt (const 0)
x = ⊤`). Contrapositively, the constant value `w` must satisfy
`w ≠ 0`. -/
theorem toFun_const_value_ne_zero
    (f : MeromorphicNonzero X) [Nonempty X]
    {w : ℂ} (h : ∀ x, f.toFun x = w) : w ≠ 0 := by
  intro hw
  -- f.toFun = const 0 ⇒ mmeromorphicOrderAt at any x = ⊤,
  -- contradicting nonvanishing_germ.
  obtain ⟨x⟩ := ‹Nonempty X›
  have h_const : f.toFun = (0 : X → ℂ) := by
    funext y
    rw [h y, hw]; rfl
  have h_order : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x = ⊤ := by
    rw [h_const]
    exact JacobianChallenge.mmeromorphicOrderAt_zero
  exact f.nonvanishing_germ x h_order

/-- **`principalDivisorMap f = 0` from `IsConstantMap f.toRiemannSphere`.**

Composition: `isConstantMap_toFun_of_isConstantMap_toRiemannSphere`
gives `IsConstantMap f.toFun` with value `w`; `toFun_const_value_ne_zero`
gives `w ≠ 0`; `orderFun_const_ne_zero` gives `orderFun f.toFun x = 0`
pointwise; `principalDivisorMap_apply` lifts to the `Finsupp` equality.

This is the named bridge needed by
`abelGeneratorPeriodCondition_of_period_and_constant_divisor_zero` to
discharge its `h_constant_divisor_zero` input. -/
theorem principalDivisorMap_eq_zero_of_isConstantMap
    (f : MeromorphicNonzero X) [Nonempty X]
    (h : JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    principalDivisorMap f = 0 := by
  -- toFun is constant with some value w.
  obtain ⟨w, hw⟩ := f.isConstantMap_toFun_of_isConstantMap_toRiemannSphere h
  -- w ≠ 0 by nonvanishing germ.
  have hw_ne : w ≠ 0 := f.toFun_const_value_ne_zero hw
  -- Show pointwise zero, then Finsupp ext.
  ext x
  show (principalDivisorMap f : X → ℤ) x = 0
  rw [principalDivisorMap_apply]
  -- orderFun f.toFun x = orderFun (const w) x = 0 (for w ≠ 0).
  have h_fun_eq : f.toFun = fun _ : X => w := by funext y; exact hw y
  rw [h_fun_eq]
  exact JacobianChallenge.MMeromorphicOn.orderFun_const_ne_zero hw_ne

end MeromorphicNonzero

end JacobianChallenge

end
