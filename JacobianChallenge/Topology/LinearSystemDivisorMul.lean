/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemDivisorMono
import Mathlib.Algebra.Algebra.Operations

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Multiplicative grading of `linearSystemDivisor`: `L(D₁) · L(D₂) ⊆ L(D₁ + D₂)`

The fundamental algebraic property of the divisor filtration on
`MeromorphicFunctionGerm X`: pointwise multiplication adds orders, and
the constraint `-D₁(y) ≤ ord_y φ` together with `-D₂(y) ≤ ord_y ψ`
gives `-(D₁ + D₂)(y) ≤ ord_y (φ · ψ)`.

This is the manifold-level germ analog of mathlib's
`meromorphicOrderAt_mul : ord (f * g) = ord f + ord g`, lifted through
the chart pullback to `MeromorphicFunctionGerm.orderAt`.

## Contents

* `MeromorphicFunctionGerm.orderAt_mul` — germ-level order of a
  product: `(φ * ψ).orderAt y = φ.orderAt y + ψ.orderAt y`.
* `IsBoundedByDivisor.mul` — `φ ∈ L(D₁), ψ ∈ L(D₂) ⟹ φ · ψ ∈ L(D₁ + D₂)`.
* `linearSystemDivisor_mul_le_linearSystemDivisor_add` — Submodule
  inclusion `L(D₁) · L(D₂) ≤ L(D₁ + D₂)` (using `Submodule.mul`).

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

/-! ## Germ-level order of a product -/

/-- **Order of a product on the germ field:**
`(φ * ψ).orderAt y = φ.orderAt y + ψ.orderAt y`.

Proved by reducing through `mk` representatives and chart pullback to
mathlib's `meromorphicOrderAt_mul`. -/
theorem MeromorphicFunctionGerm.orderAt_mul
    (φ ψ : MeromorphicFunctionGerm X) (y : X) :
    (φ * ψ).orderAt y = φ.orderAt y + ψ.orderAt y := by
  rcases φ with ⟨f⟩
  rcases ψ with ⟨g⟩
  -- Reduce the germ-level product to `mk (f * g)`.
  show MeromorphicFunctionGerm.orderAt y
      (MeromorphicFunctionGerm.mk f * MeromorphicFunctionGerm.mk g) = _
  rw [MeromorphicFunctionGerm.mk_mul, MeromorphicFunctionGerm.orderAt_mk]
  -- `(f * g).toFun = f.toFun * g.toFun` definitionally.
  have h_unfold_toFun : (f * g).toFun = f.toFun * g.toFun := rfl
  rw [h_unfold_toFun]
  -- Drop to the chart pullback.
  show meromorphicOrderAt
      ((f.toFun * g.toFun) ∘ (chartAt ℂ y).symm) ((chartAt ℂ y) y) = _
  have h_chart_unfold :
      (f.toFun * g.toFun) ∘ (chartAt ℂ y).symm
        = (f.toFun ∘ (chartAt ℂ y).symm)
            * (g.toFun ∘ (chartAt ℂ y).symm) := rfl
  rw [h_chart_unfold]
  -- Apply mathlib's `meromorphicOrderAt_mul`.
  have hxf : MMeromorphicAt (𝓘(ℂ, ℂ)) f.toFun y := f.mmero y (Set.mem_univ y)
  have hxg : MMeromorphicAt (𝓘(ℂ, ℂ)) g.toFun y := g.mmero y (Set.mem_univ y)
  exact meromorphicOrderAt_mul hxf hxg

/-! ## `IsBoundedByDivisor` under multiplication -/

/-- **`L(D₁) · L(D₂) ⊆ L(D₁ + D₂)` pointwise:** if `φ ∈ L(D₁)` and
`ψ ∈ L(D₂)`, then `φ · ψ ∈ L(D₁ + D₂)`. -/
lemma IsBoundedByDivisor.mul
    {D₁ D₂ : JacobianChallenge.Div X}
    {φ ψ : MeromorphicFunctionGerm X}
    (hφ : IsBoundedByDivisor D₁ φ) (hψ : IsBoundedByDivisor D₂ ψ) :
    IsBoundedByDivisor (D₁ + D₂) (φ * ψ) := by
  intro y
  -- `ord_y (φ * ψ) = ord_y φ + ord_y ψ ≥ -D₁(y) + -D₂(y) = -(D₁ + D₂)(y)`.
  rw [MeromorphicFunctionGerm.orderAt_mul]
  -- Rewrite `-((D₁ + D₂) y)` to `-(D₁ y) + -(D₂ y)` in ℤ, then cast.
  have h_coe_add : (D₁ + D₂) y = D₁ y + D₂ y :=
    Function.locallyFinsuppWithin.coe_add D₁ D₂ ▸ rfl
  have h_neg_int : (-((D₁ + D₂) y) : ℤ) = (-(D₁ y) : ℤ) + (-(D₂ y) : ℤ) := by
    rw [h_coe_add]; ring
  have h_cast : ((-((D₁ + D₂) y) : ℤ) : WithTop ℤ)
      = ((-(D₁ y) : ℤ) : WithTop ℤ) + ((-(D₂ y) : ℤ) : WithTop ℤ) := by
    rw [h_neg_int]
    push_cast
    rfl
  rw [h_cast]
  exact add_le_add (hφ y) (hψ y)

/-! ## Submodule-level multiplicative grading -/

/-- **`L(D₁) · L(D₂) ≤ L(D₁ + D₂)`** as `Submodule ℂ`-multiplication.

This is the multiplicative grading of the divisor filtration on the
germ field: the L(D) family is a graded ℂ-subalgebra structure
inside `MeromorphicFunctionGerm X`. -/
theorem linearSystemDivisor_mul_le_linearSystemDivisor_add
    (D₁ D₂ : JacobianChallenge.Div X) :
    (linearSystemDivisor D₁) * (linearSystemDivisor D₂)
      ≤ linearSystemDivisor (D₁ + D₂) := by
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ
  rw [mem_linearSystemDivisor] at hφ hψ
  rw [mem_linearSystemDivisor]
  exact IsBoundedByDivisor.mul hφ hψ

end JacobianChallenge.MeromorphicFunctionField

end
