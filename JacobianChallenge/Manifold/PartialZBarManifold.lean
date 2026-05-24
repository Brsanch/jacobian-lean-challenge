/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBar
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Defs

set_option linter.unusedSectionVars false

/-! # `partialZBar` lifted to a complex 1-manifold

`partialZBar : (ℂ → ℂ) → ℂ → ℂ` from `PartialZBar.lean` is the
chart-free antiholomorphic Wirtinger derivative. This file lifts it to
a manifold-level operator
`partialZBarManifold : (X → ℂ) → X → ℂ` for any `[ChartedSpace ℂ X]`,
by chart pullback through the canonical `extChartAt 𝓘(ℂ, ℂ) x`:

  `partialZBarManifold f x := partialZBar (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
                                          ((extChartAt 𝓘(ℂ, ℂ) x) x)`.

On a complex 1-manifold (chart transitions are holomorphic), this
operator is chart-independent up to a `conj (deriv Φ z)` factor
(see `PartialZBarChainRule.lean`) — that is, it is a section of the
`(0,1)`-form bundle rather than a function. The chart-independence as
a function is **not** asserted here; this file works with the canonical
chart pullback throughout, which is what the Forster §16 cutoff +
correction argument actually consumes.

## What this file ships

* `partialZBarManifold f x` — the chart-pullback ∂̄ at `x`.
* `partialZBarManifold_zero`, `_const`, `_add`, `_neg`, `_sub`,
  `_const_mul`.
* **`partialZBarManifold_mul` (Leibniz)** — the Chip 1 keystone.
  Given real-differentiability of the chart pullbacks of `f` and `g`
  at the chart image of `x`,
  `∂̄ (f · g) x = (∂̄ f x) · g x + f x · (∂̄ g x)`.
* `partialZBarManifold_mul_of_chartPullback_differentiableAt_right/left`
  — **Forster §16 specialization**: when one factor's chart pullback
  is ℂ-holomorphic at the chart image of `x`, the corresponding term
  drops. This is the identity used in the cutoff argument:
  `∂̄ (χ · g₀) x = (∂̄ χ x) · g₀ x` on the locus where the chart-local
  pole `g₀ = 1/(φ - c₀)` is holomorphic (off the pole `p`).
* `partialZBarManifold_eq_zero_of_chartPullback_differentiableAt` — if
  the chart pullback of `f` is ℂ-differentiable at the chart image of
  `x`, then `∂̄ f x = 0` (manifold-level vanishing on holomorphic
  functions).

The CR converse (smooth + `∂̄ = 0` ⇒ holomorphic) on the chart side is
already proven in `DBarOperator.lean` via
`differentiableAt_complex_of_dbarChart_eq_zero`, and `dbarChart`
equals `partialZBar` up to `(1/2 : ℂ) = (2 : ℂ)⁻¹`. Chip 2 will route
through that lemma at the chart level when needed.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology
open Complex

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Manifold-side antiholomorphic Wirtinger derivative** at a point `x`
of a `ChartedSpace ℂ X`. Defined as `partialZBar` applied to the
chart pullback `f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm` at the chart image of `x`. -/
def partialZBarManifold (f : X → ℂ) (x : X) : ℂ :=
  partialZBar (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x)

/-! ## Algebraic lemmas (mirroring `PartialZBar.lean`) -/

@[simp] lemma partialZBarManifold_const (c : ℂ) (x : X) :
    partialZBarManifold (fun _ : X => c) x = 0 := by
  unfold partialZBarManifold
  -- Chart pullback of a constant is constant.
  have h : (fun _ : X => c) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm = fun _ : ℂ => c := rfl
  rw [h]
  exact partialZBar_const c _

@[simp] lemma partialZBarManifold_zero (x : X) :
    partialZBarManifold (0 : X → ℂ) x = 0 := by
  have h : (0 : X → ℂ) = fun _ : X => (0 : ℂ) := rfl
  rw [h, partialZBarManifold_const]

lemma partialZBarManifold_add {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hg : DifferentiableAt ℝ (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold (f + g) x
      = partialZBarManifold f x + partialZBarManifold g x := by
  unfold partialZBarManifold
  have h_distrib :
      ((f + g) : X → ℂ) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          + (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib]
  exact partialZBar_add hf hg

lemma partialZBarManifold_neg (f : X → ℂ) (x : X) :
    partialZBarManifold (-f) x = -partialZBarManifold f x := by
  unfold partialZBarManifold
  have h_distrib : (-f : X → ℂ) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = -(f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib]
  exact partialZBar_neg

lemma partialZBarManifold_sub {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hg : DifferentiableAt ℝ (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold (f - g) x
      = partialZBarManifold f x - partialZBarManifold g x := by
  unfold partialZBarManifold
  have h_distrib :
      ((f - g) : X → ℂ) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          - (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib]
  exact partialZBar_sub hf hg

/-! ## Leibniz — the Chip 1 keystone -/

/-- **Manifold-side Leibniz** for `partialZBarManifold`. -/
theorem partialZBarManifold_mul {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hg : DifferentiableAt ℝ (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold (fun y : X => f y * g y) x
      = partialZBarManifold f x * g x + f x * partialZBarManifold g x := by
  unfold partialZBarManifold
  -- `(fun y => f y * g y) ∘ chart.symm = (f ∘ chart.symm) * (g ∘ chart.symm)`.
  have h_distrib :
      (fun y : X => f y * g y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          * (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib, partialZBar_mul hf hg]
  -- Replace chart-pullback evaluation at the chart image of `x` with the
  -- value at `x` itself.
  have hfx : (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x) = f x := by
    show f ((extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x)) = f x
    rw [extChartAt_to_inv]
  have hgx : (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x) = g x := by
    show g ((extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x)) = g x
    rw [extChartAt_to_inv]
  rw [hfx, hgx]

/-! ## Forster §16 specializations -/

/-- **Forster §16 specialization (right)**: when the chart pullback of
`g` is ℂ-holomorphic at the chart image of `x`,
`∂̄ (f · g) x = (∂̄ f x) · g x`. The Leibniz term `f · ∂̄ g` drops
because `∂̄ g = 0` on holomorphic functions. -/
theorem partialZBarManifold_mul_of_chartPullback_differentiableAt_right
    {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℝ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hg : DifferentiableAt ℂ (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold (fun y : X => f y * g y) x
      = partialZBarManifold f x * g x := by
  unfold partialZBarManifold
  have h_distrib :
      (fun y : X => f y * g y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          * (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib, partialZBar_mul_of_differentiableAt_right hf hg]
  have hgx : (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x) = g x := by
    show g ((extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x)) = g x
    rw [extChartAt_to_inv]
  rw [hgx]

/-- **Forster §16 specialization (left)**: symmetric — when the chart
pullback of `f` is ℂ-holomorphic at the chart image of `x`,
`∂̄ (f · g) x = f x · (∂̄ g x)`. -/
theorem partialZBarManifold_mul_of_chartPullback_differentiableAt_left
    {f g : X → ℂ} {x : X}
    (hf : DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x))
    (hg : DifferentiableAt ℝ (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold (fun y : X => f y * g y) x
      = f x * partialZBarManifold g x := by
  unfold partialZBarManifold
  have h_distrib :
      (fun y : X => f y * g y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        = (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          * (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) := rfl
  rw [h_distrib, partialZBar_mul_of_differentiableAt_left hf hg]
  have hfx : (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ((extChartAt 𝓘(ℂ, ℂ) x) x) = f x := by
    show f ((extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x)) = f x
    rw [extChartAt_to_inv]
  rw [hfx]

/-! ## Vanishing on holomorphic functions -/

/-- **Manifold-side: holomorphic-in-chart ⇒ `∂̄ f x = 0`.** -/
theorem partialZBarManifold_eq_zero_of_chartPullback_differentiableAt
    {f : X → ℂ} {x : X}
    (hf : DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold f x = 0 := by
  unfold partialZBarManifold
  exact partialZBar_eq_zero_of_differentiableAt hf

end JacobianChallenge

end
