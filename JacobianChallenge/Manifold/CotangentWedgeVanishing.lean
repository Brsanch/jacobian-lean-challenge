/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Cotangent
import JacobianChallenge.Manifold.HolomorphicOneForm

set_option linter.unusedSectionVars false

/-! # Pointwise type-(2,0)-vanishing on a complex 1-manifold

For a complex 1-manifold `X` (i.e. `ChartedSpace ℂ X` + `IsManifold
𝓘(ℂ, ℂ) ω X`), every cotangent space is `ℂ →L[ℂ] ℂ` — a 1-dimensional
ℂ-vector space. The alternating bilinear form built from two cotangent
vectors

  `(a, b) ↦ v a * w b - v b * w a`

is therefore identically zero on `ℂ × ℂ`. This is the **pointwise
type-(2,0)-vanishing** — the foundational classical fact that drives
Riemann's first bilinear relation for holomorphic 1-forms on a Riemann
surface:

  for `ω, η : HolomorphicOneForm X`, the wedge product `ω ∧ η` is a
  type-(2,0) form on a 1-complex-dim manifold, hence identically zero.

This file ships the pure linear-algebra core. Higher-level integration
identities (e.g. `∫_X ω ∧ η = 0`, and from there the strict-upper
triangular vanishing of `pmatᵀ · J · pmat` at general genus) build on
this fact via differential-form infrastructure.

## What this file ships

* `cotangent_wedge_pointwise_zero` — the alternating bilinear product
  `v a * w b - v b * w a` vanishes for all `v, w : ℂ →L[ℂ] ℂ` and
  `a, b : ℂ`. Pure ℂ-linear algebra, no manifold premise required.
* `CotangentSpace.wedge_pointwise_zero` — the same statement specialised
  to `CotangentSpace 𝓘(ℂ, ℂ) x` for `x : X` on a complex 1-manifold.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open ContinuousLinearMap

namespace JacobianChallenge

/-- **Pointwise type-(2,0)-vanishing (pure ℂ-linear algebra).**

For any two continuous ℂ-linear functionals `v, w : ℂ →L[ℂ] ℂ` and any
`a, b : ℂ`, the alternating bilinear product `v a * w b - v b * w a`
vanishes.

Proof. Every continuous ℂ-linear functional on `ℂ` is multiplication by
a scalar: `v a = v 1 * a`, `w a = w 1 * a`. Substituting gives
`v 1 * a * (w 1 * b) - v 1 * b * (w 1 * a)`, which is zero by
commutativity. -/
theorem cotangent_wedge_pointwise_zero
    (v w : ℂ →L[ℂ] ℂ) (a b : ℂ) :
    v a * w b - v b * w a = 0 := by
  have hv : ∀ z : ℂ, v z = v 1 * z := fun z => by
    have h : v z = v (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    rw [h, map_smul, smul_eq_mul, mul_comm]
  have hw : ∀ z : ℂ, w z = w 1 * z := fun z => by
    have h : w z = w (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    rw [h, map_smul, smul_eq_mul, mul_comm]
  rw [hv a, hw b, hv b, hw a]
  ring

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Pointwise type-(2,0)-vanishing on a complex 1-manifold.**

For any point `x : X` of a complex 1-manifold and any two cotangent
vectors `v, w : CotangentSpace 𝓘(ℂ, ℂ) x`, the alternating bilinear
product vanishes on every pair of tangent inputs `a, b : ℂ`.

`CotangentSpace 𝓘(ℂ, ℂ) x` is the non-reducible synonym for
`ℂ →L[ℂ] ℂ`, so the result is stated through the canonical coercion
`(v : ℂ →L[ℂ] ℂ)`. Direct specialisation of
`cotangent_wedge_pointwise_zero`. -/
theorem CotangentSpace.wedge_pointwise_zero
    (x : X) (v w : CotangentSpace (𝓘(ℂ, ℂ)) x) (a b : ℂ) :
    (show ℂ →L[ℂ] ℂ from v) a * (show ℂ →L[ℂ] ℂ from w) b
        - (show ℂ →L[ℂ] ℂ from v) b * (show ℂ →L[ℂ] ℂ from w) a = 0 :=
  cotangent_wedge_pointwise_zero _ _ a b

end JacobianChallenge

end
