/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentWedgeAlternating
import JacobianChallenge.Manifold.HolomorphicOneFormRealification

set_option linter.unusedSectionVars false

/-! # Pointwise wedge of holomorphic 1-forms

Given two holomorphic 1-forms `ω, η : HolomorphicOneForm X` on a
complex 1-manifold `X`, the pointwise wedge `(ω ∧ η)(x)` is the
cotangent wedge of `ω.eval x` and `η.eval x` (chip 13). Since the
second exterior power of `ℂ →L[ℂ] ℂ` is zero, this is identically
the zero `AlternatingMap` at every point.

Lifts chip 13 from "per-cotangent-vector pair at a point" to
"per-pair-of-1-form sections, point-by-point on `X`".

## What this file ships

* `holomorphicOneFormWedge ω η : X → AlternatingMap ℂ ℂ ℂ (Fin 2)`
  — pointwise wedge function.
* `holomorphicOneFormWedge_apply` — at every `x`, the wedge is the
  cotangent wedge of the eval values.
* `holomorphicOneFormWedge_eq_zero` — identically zero (chip 13).
* `holomorphicOneFormWedge_apply_pointwise` — at every `x` and every
  `v : Fin 2 → ℂ`, the wedge evaluates to `0` (chip 5 / chip 13).
* `holomorphicOneFormWedge_formula` — pointwise formula
  `(ω ∧ η)(x) v = (ω.eval x)(v 0) · (η.eval x)(v 1) - …`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Pointwise wedge of two holomorphic 1-forms.** At every `x : X`,
this is the cotangent wedge `cotangentWedge (ω.eval x) (η.eval x)`,
which lives in the zero `AlternatingMap ℂ ℂ ℂ (Fin 2)`. -/
noncomputable def holomorphicOneFormWedge
    (om₀ om₁ : HolomorphicOneForm X) :
    X → AlternatingMap ℂ ℂ ℂ (Fin 2) :=
  fun x => cotangentWedge (om₀.eval x) (om₁.eval x)

/-- **The pointwise wedge as the cotangent wedge of the eval values.** -/
theorem holomorphicOneFormWedge_apply
    (om₀ om₁ : HolomorphicOneForm X) (x : X) :
    holomorphicOneFormWedge om₀ om₁ x
      = cotangentWedge (om₀.eval x) (om₁.eval x) := rfl

/-- **The pointwise wedge is identically the zero alternating map.**
Direct from chip 13 (`cotangentWedge_eq_zero` would say the wedge is
`0`; here `cotangentWedge` is *defined* as `0`, so the result is
`rfl`-ish). -/
@[simp]
theorem holomorphicOneFormWedge_eq_zero
    (om₀ om₁ : HolomorphicOneForm X) :
    holomorphicOneFormWedge om₀ om₁ = fun _ => 0 := by
  funext x
  rfl

/-- **The wedge evaluates to `0` at every point and on every vector pair.** -/
theorem holomorphicOneFormWedge_apply_pointwise
    (om₀ om₁ : HolomorphicOneForm X) (x : X) (v : Fin 2 → ℂ) :
    holomorphicOneFormWedge om₀ om₁ x v = 0 := by
  rw [holomorphicOneFormWedge_apply, cotangentWedge_apply]

/-- **Pointwise wedge formula.** At any `x` and any `v : Fin 2 → ℂ`,
the wedge unpacks to the alternating bilinear expression
`(ω.eval x)(v 0) · (η.eval x)(v 1) - (ω.eval x)(v 1) · (η.eval x)(v 0)`.
By chip 5 this expression is identically `0`. -/
theorem holomorphicOneFormWedge_formula
    (om₀ om₁ : HolomorphicOneForm X) (x : X) (v : Fin 2 → ℂ) :
    holomorphicOneFormWedge om₀ om₁ x v
      = (om₀.eval x) (v 0) * (om₁.eval x) (v 1)
          - (om₀.eval x) (v 1) * (om₁.eval x) (v 0) := by
  rw [holomorphicOneFormWedge_apply]
  exact cotangentWedge_formula (om₀.eval x) (om₁.eval x) v

end JacobianChallenge

end
