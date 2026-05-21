/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DBarOperator
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option linter.unusedSectionVars false

/-! # `dbar` (`∂̄`) lifted to a complex 1-manifold

This file lifts the chart-side `dbarChart` from `DBarOperator.lean` to
a manifold-level operator `dbar : (X → ℂ) → X → ℂ` for any
`[ChartedSpace ℂ X]`. The definition uses the canonical extended chart
`extChartAt 𝓘(ℂ, ℂ) x`:

  `dbar f x := dbarChart (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
                          ((extChartAt 𝓘(ℂ, ℂ) x) x)`.

On a *complex* 1-manifold (chart transitions are holomorphic), this
operator is in fact chart-independent — `dbar f x` does not depend on
which holomorphic chart around `x` we picked. That global
well-definedness is a follow-up chip; this file proves only:

* `dbar_const x = 0` (chart-side constants pull back to chart-side
  constants).
* `dbar_zero x = 0`.
* `dbar_add` (additivity).
* **Holomorphic-in-chart ⇒ `dbar f x = 0`**: if the chart-pullback
  `f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm` is ℂ-differentiable at the chart
  point `(extChartAt 𝓘(ℂ, ℂ) x) x`, then `dbar f x = 0`. This is the
  manifold-level statement that holomorphic functions have vanishing
  `∂̄`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Manifold-side `∂̄f(x)`** at a point `x` of a `ChartedSpace ℂ X`.
Pulls `f : X → ℂ` back through the canonical chart at `x`, then
evaluates `dbarChart` at the chart image of `x`. -/
def dbar (f : X → ℂ) (x : X) : ℂ :=
  dbarChart (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x)

@[simp] lemma dbar_const (c : ℂ) (x : X) :
    dbar (fun _ : X => c) x = 0 := by
  unfold dbar
  -- The pullback of a constant is a constant.
  have h : (fun _ : X => c) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm = fun _ : ℂ => c := rfl
  rw [h, dbarChart_const]

@[simp] lemma dbar_zero (x : X) :
    dbar (0 : X → ℂ) x = 0 := by
  have h : (0 : X → ℂ) = fun _ : X => (0 : ℂ) := rfl
  rw [h, dbar_const]

lemma dbar_add {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hg : DifferentiableAt ℝ (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    dbar (f + g) x = dbar f x + dbar g x := by
  unfold dbar
  -- `(f + g) ∘ ψ = f ∘ ψ + g ∘ ψ` by ext.
  have h_distrib :
      ((f + g) : X → ℂ) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          + (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib]
  exact dbarChart_add hf hg

lemma dbar_neg (f : X → ℂ) (x : X) :
    dbar (-f) x = -dbar f x := by
  unfold dbar
  -- `(-f) ∘ ψ = -(f ∘ ψ)` by ext.
  have h_distrib : (-f : X → ℂ) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = -(f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib]
  exact dbarChart_neg _ _

/-- **ℂ-scalar linearity of `dbar`.** `dbar (fun y => c * f y) x = c * dbar f x`. -/
lemma dbar_const_mul (c : ℂ) (f : X → ℂ) (x : X) :
    dbar (fun y : X => c * f y) x = c * dbar f x := by
  unfold dbar
  have h_distrib : (fun y : X => c * f y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
      = fun z : ℂ => c * (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z := rfl
  rw [h_distrib]
  exact dbarChart_const_mul _ _ _

/-- **Holomorphic-in-chart ⇒ `∂̄f = 0` at that point.**

If the chart-pullback `f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm : ℂ → ℂ` is
ℂ-differentiable at the chart image of `x`, then the manifold-side
`∂̄`-operator vanishes at `x`.

This is the manifold analogue of `dbarChart_eq_zero_of_hasDerivAt`. -/
theorem dbar_eq_zero_of_chartPullback_hasDerivAt {f : X → ℂ} {x : X}
    {f' : ℂ}
    (hf : HasDerivAt (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) f'
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    dbar f x = 0 := by
  unfold dbar
  exact dbarChart_eq_zero_of_hasDerivAt hf

/-- **Holomorphic-in-chart ⇒ `∂̄f = 0`**, `DifferentiableAt ℂ` form. -/
theorem dbar_eq_zero_of_chartPullback_differentiableAt {f : X → ℂ} {x : X}
    (hf : DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    dbar f x = 0 :=
  dbar_eq_zero_of_chartPullback_hasDerivAt hf.hasDerivAt

end JacobianChallenge

end
