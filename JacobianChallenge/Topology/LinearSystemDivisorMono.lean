/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDivisorConstants
import JacobianChallenge.Topology.LinearSystemDivisorZeroLiouville

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Monotonicity of `linearSystemDivisor` in the divisor

The structural fact `D₁ ≤ D₂ ⟹ L(D₁) ≤ L(D₂)` on the germ field.
Pointwise: if `D₁ y ≤ D₂ y` for every `y`, then `-D₂(y) ≤ -D₁(y) ≤
ord_y φ` whenever `φ ∈ L(D₁)`, so `φ ∈ L(D₂)`. Monotonicity for
divisors with the pointwise `≤` from
`Function.locallyFinsuppWithin.le_def`.

## Contents

* `IsBoundedByDivisor.mono` — pointwise monotonicity of the predicate.
* `linearSystemDivisor_mono` — `D₁ ≤ D₂ → linearSystemDivisor D₁ ≤
  linearSystemDivisor D₂` as a `Submodule` inclusion.
* `linearSystemDivisor_zero_le_of_effective` — `L(0) ≤ L(D)` for any
  effective divisor `D` (`0 ≤ D`).
* `constantsGerm_le_linearSystemDivisor_of_effective` —
  `constantsGerm X ≤ linearSystemDivisor D` for effective `D`,
  factoring `constantsGerm ≤ L(0) ≤ L(D)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Pointwise monotonicity -/

/-- **`IsBoundedByDivisor` is monotone in the divisor.** If `D₁ ≤ D₂`
(pointwise), then membership in `L(D₁)` implies membership in `L(D₂)`. -/
lemma IsBoundedByDivisor.mono
    {D₁ D₂ : JacobianChallenge.Div X} (hD : D₁ ≤ D₂)
    {φ : MeromorphicFunctionGerm X}
    (hφ : IsBoundedByDivisor D₁ φ) :
    IsBoundedByDivisor D₂ φ := by
  intro y
  -- `-D₂(y) ≤ -D₁(y) ≤ ord_y φ`.
  have h_le_at : D₁ y ≤ D₂ y :=
    (Function.locallyFinsuppWithin.le_def.mp hD) y
  have h_neg_le : (-(D₂ y) : ℤ) ≤ (-(D₁ y) : ℤ) := by omega
  have h_cast : ((-(D₂ y) : ℤ) : WithTop ℤ) ≤ ((-(D₁ y) : ℤ) : WithTop ℤ) := by
    exact_mod_cast h_neg_le
  exact h_cast.trans (hφ y)

/-! ## Submodule monotonicity -/

/-- **`linearSystemDivisor` is monotone in the divisor**: `D₁ ≤ D₂ →
linearSystemDivisor D₁ ≤ linearSystemDivisor D₂`. -/
theorem linearSystemDivisor_mono
    {D₁ D₂ : JacobianChallenge.Div X} (hD : D₁ ≤ D₂) :
    linearSystemDivisor D₁ ≤ linearSystemDivisor D₂ := by
  intro φ hφ
  rw [mem_linearSystemDivisor] at hφ ⊢
  exact IsBoundedByDivisor.mono hD hφ

/-! ## `L(0) ≤ L(D)` for effective divisors -/

/-- Effective divisors dominate the zero divisor: `(0 : Div X) ≤ D`
when `∀ y, 0 ≤ D y`. -/
lemma le_of_effective {D : JacobianChallenge.Div X} (hD : ∀ y, 0 ≤ D y) :
    (0 : JacobianChallenge.Div X) ≤ D := by
  rw [Function.locallyFinsuppWithin.le_def]
  intro y
  show ((0 : JacobianChallenge.Div X) y : ℤ) ≤ D y
  -- `(0 : Div X) y = 0`.
  rw [show ((0 : JacobianChallenge.Div X) y) = (0 : ℤ) from rfl]
  exact hD y

/-- **`L(0) ≤ L(D)` for effective `D`.** All globally holomorphic
germs sit inside `L(D)` for any effective `D`. -/
theorem linearSystemDivisor_zero_le_of_effective
    {D : JacobianChallenge.Div X} (hD : ∀ y, 0 ≤ D y) :
    linearSystemDivisor (0 : JacobianChallenge.Div X) ≤ linearSystemDivisor D :=
  linearSystemDivisor_mono (le_of_effective hD)

end JacobianChallenge.MeromorphicFunctionField

/-! ## Constants factoring through `L(0)` into `L(D)` for effective `D` -/

namespace JacobianChallenge.MeromorphicFunctionField

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`constantsGerm X ≤ linearSystemDivisor D` for effective `D`.**

This is a structural consequence: `constantsGerm = span ℂ {1} =
linearSystemDivisor 0` (under Liouville), and
`linearSystemDivisor 0 ≤ linearSystemDivisor D` for effective `D` by
monotonicity. The intermediate equality
`linearSystemDivisor 0 = constantsGerm X` is the unconditional headline
of `Topology/LinearSystemDivisorZeroLiouville.lean`. -/
theorem constantsGerm_le_linearSystemDivisor_of_effective
    {D : JacobianChallenge.Div X} (hD : ∀ y, 0 ≤ D y) :
    constantsGerm X ≤ linearSystemDivisor D := by
  -- `constantsGerm X = linearSystemDivisor 0` (unconditional, via Liouville).
  rw [← linearSystemDivisor_zero_eq_constantsGerm_unconditional]
  exact linearSystemDivisor_zero_le_of_effective hD

end JacobianChallenge.MeromorphicFunctionField

end
