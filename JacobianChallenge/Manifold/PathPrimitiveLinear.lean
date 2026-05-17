/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrimitiveOnSmoothPathConnected
import JacobianChallenge.Manifold.ComplexChainPeriodFormLinear

set_option linter.unusedSectionVars false

/-! # Linearity of `pathPrimitive` in the 1-form argument

The `pathPrimitive` construction is additive (and respects zero / neg)
in its `om` argument, inherited from `complexChainPeriod`'s
`AddMonoidHom` structure in the form.

This factors `PathPrimitiveSmoothness` and `PathPrimitiveFTC` through a
chosen ℂ-basis of `HolomorphicOneForm X`: smoothness / FTC at each basis
element gives smoothness / FTC at every form via linearity.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]

/-- `pathPrimitive` at the zero form is the zero function. -/
@[simp] theorem pathPrimitive_zero
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X) :
    pathPrimitive h_conn x₀ (0 : HolomorphicOneForm X) = fun _ => 0 := by
  funext x
  unfold pathPrimitive
  rw [complexChainPeriod_zero_right]

/-- `pathPrimitive` is additive in the form argument. -/
theorem pathPrimitive_add
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (om₁ om₂ : HolomorphicOneForm X) :
    pathPrimitive h_conn x₀ (om₁ + om₂)
      = fun x => pathPrimitive h_conn x₀ om₁ x + pathPrimitive h_conn x₀ om₂ x := by
  funext x
  unfold pathPrimitive
  exact complexChainPeriod_add_right _ om₁ om₂

/-- `pathPrimitive` negates with the form argument. -/
theorem pathPrimitive_neg
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (om : HolomorphicOneForm X) :
    pathPrimitive h_conn x₀ (-om)
      = fun x => -pathPrimitive h_conn x₀ om x := by
  funext x
  unfold pathPrimitive
  exact complexChainPeriod_neg_right _ om

/-- `pathPrimitive` is ℂ-scalable in the form argument. -/
theorem pathPrimitive_smul
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X)
    (z : ℂ) (om : HolomorphicOneForm X) :
    pathPrimitive h_conn x₀ (z • om)
      = fun x => z * pathPrimitive h_conn x₀ om x := by
  funext x
  unfold pathPrimitive
  exact complexChainPeriod_smul_complex_right _ z om

/-- **`pathPrimitive` as an `AddMonoidHom` in the form argument** (at a
fixed evaluation point `x`). -/
def pathPrimitiveHom
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ : X) (x : X) :
    HolomorphicOneForm X →+ ℂ where
  toFun om := pathPrimitive h_conn x₀ om x
  map_zero' := by
    simp [pathPrimitive_zero]
  map_add' om₁ om₂ := by
    have := pathPrimitive_add h_conn x₀ om₁ om₂
    show pathPrimitive h_conn x₀ (om₁ + om₂) x
      = pathPrimitive h_conn x₀ om₁ x + pathPrimitive h_conn x₀ om₂ x
    rw [this]

@[simp] theorem pathPrimitiveHom_apply
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ x : X)
    (om : HolomorphicOneForm X) :
    pathPrimitiveHom h_conn x₀ x om = pathPrimitive h_conn x₀ om x := rfl

/-- **`pathPrimitive` as a ℂ-linear functional** at a fixed evaluation
point `x`. -/
noncomputable def pathPrimitiveLinearMap
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ x : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun om := pathPrimitive h_conn x₀ om x
  map_add' om₁ om₂ := by
    have := pathPrimitive_add h_conn x₀ om₁ om₂
    show pathPrimitive h_conn x₀ (om₁ + om₂) x
      = pathPrimitive h_conn x₀ om₁ x + pathPrimitive h_conn x₀ om₂ x
    rw [this]
  map_smul' z om := by
    show pathPrimitive h_conn x₀ (z • om) x
      = z • pathPrimitive h_conn x₀ om x
    rw [pathPrimitive_smul]
    rfl

@[simp] theorem pathPrimitiveLinearMap_apply
    (h_conn : SmoothPathConnected 𝓘(ℝ, ℂ) X) (x₀ x : X)
    (om : HolomorphicOneForm X) :
    pathPrimitiveLinearMap h_conn x₀ x om = pathPrimitive h_conn x₀ om x := rfl

end JacobianChallenge

end
