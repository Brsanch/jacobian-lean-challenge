/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartPompeiuKernel
import Mathlib.Algebra.BigOperators.Pi

/-! # Chart-anchored manifold-side `∂̄` (Sub-chip 5.5a, Path A)

`PartialZBarManifold.lean` defines

  `partialZBarManifold f x := partialZBar (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
                                          ((extChartAt 𝓘(ℂ, ℂ) x) x)`

i.e. the chart pullback is taken via the **canonical chart at `x`** —
the same point at which the operator is evaluated. For a partition-of-
unity construction whose summands `v_i` are built via **the chart at a
fixed anchor `x_i`** (e.g. via `pompeiuKernel(... ∘ chart_xi)`), this
"chart-at-evaluation-point" choice produces a conjugate-derivative
factor `conj(deriv (chart_y ∘ chart_xi.symm)(chart_xi y))` in the
per-`i` recovery identity (cf. Sub-chip 5.4c-final).

This file introduces the **chart-anchored** variant

  `partialZBarManifoldAtChart x f y :=
     partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)`,

which evaluates `partialZBar` of the **chart-at-`x` pullback** of `f`
at `(chartAt ℂ x) y`, regardless of how the canonical chart at `y`
relates to the canonical chart at `x`. This is exactly the chart-x
view operator that appeared inside Chip 4's bridge. With anchor `x`
fixed across all summands of a partition sum, the factor `conj(τ_i)`
that varied with `i` no longer appears per-summand; it is consumed
once, at the end, by the transfer lemma below.

## What this file ships

* `partialZBarManifoldAtChart x f y` — the chart-anchored ∂̄.
* `partialZBarManifoldAtChart_zero`, `_const`, `_add`, `_neg`, `_sub`
  — algebra (parallel to `partialZBarManifold`'s API).
* `partialZBarManifoldAtChart_finset_sum` — distributivity over
  `Finset.sum`, mirroring `PartialZBarManifoldFinsetSum`.
* `partialZBarManifoldAtChart_eq_manifold_mul_transition` — the
  **transfer lemma**: for `y ∈ (chartAt ℂ x).source` with the
  appropriate differentiability,
  `partialZBarManifoldAtChart x f y
     = partialZBarManifold f y
       * conj(deriv (chart_y ∘ chart_x.symm) (chart_x y))`.
  This is a re-export of the existing content-agnostic Chip 4 bridge
  `partialZBar_chart_x_eq_manifold_mul_transition`.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Chart-anchored manifold-side `∂̄`** at anchor `x : X` of
`f : X → ℂ`, evaluated at `y : X`. Defined as `partialZBar` applied to
the **chart-at-`x` pullback** `f ∘ (chartAt ℂ x).symm` at the chart-`x`
image of `y`.

Unlike `partialZBarManifold f y` (which uses the chart at `y`), this
operator's chart depends only on the anchor `x`, not on the evaluation
point `y`. The two are related by the chart-transition factor on
`y ∈ (chartAt ℂ x).source`; see
`partialZBarManifoldAtChart_eq_manifold_mul_transition`. -/
def partialZBarManifoldAtChart (x : X) (f : X → ℂ) (y : X) : ℂ :=
  partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)

/-! ## Algebra (parallel to `PartialZBarManifold.lean`) -/

@[simp] lemma partialZBarManifoldAtChart_const (x : X) (c : ℂ) (y : X) :
    partialZBarManifoldAtChart x (fun _ : X => c) y = 0 := by
  unfold partialZBarManifoldAtChart
  have h : (fun _ : X => c) ∘ (chartAt ℂ x).symm = fun _ : ℂ => c := rfl
  rw [h]
  exact partialZBar_const c _

@[simp] lemma partialZBarManifoldAtChart_zero (x y : X) :
    partialZBarManifoldAtChart x (0 : X → ℂ) y = 0 := by
  have h : (0 : X → ℂ) = fun _ : X => (0 : ℂ) := rfl
  rw [h, partialZBarManifoldAtChart_const]

lemma partialZBarManifoldAtChart_add {f g : X → ℂ} {x y : X}
    (hf : DifferentiableAt ℝ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hg : DifferentiableAt ℝ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) :
    partialZBarManifoldAtChart x (f + g) y
      = partialZBarManifoldAtChart x f y + partialZBarManifoldAtChart x g y := by
  unfold partialZBarManifoldAtChart
  have h_distrib :
      ((f + g) : X → ℂ) ∘ (chartAt ℂ x).symm
        = (f ∘ (chartAt ℂ x).symm) + (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h_distrib]
  exact partialZBar_add hf hg

lemma partialZBarManifoldAtChart_neg (f : X → ℂ) (x y : X) :
    partialZBarManifoldAtChart x (-f) y = -partialZBarManifoldAtChart x f y := by
  unfold partialZBarManifoldAtChart
  have h_distrib : (-f : X → ℂ) ∘ (chartAt ℂ x).symm
        = -(f ∘ (chartAt ℂ x).symm) := rfl
  rw [h_distrib]
  exact partialZBar_neg

lemma partialZBarManifoldAtChart_sub {f g : X → ℂ} {x y : X}
    (hf : DifferentiableAt ℝ (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
    (hg : DifferentiableAt ℝ (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) :
    partialZBarManifoldAtChart x (f - g) y
      = partialZBarManifoldAtChart x f y - partialZBarManifoldAtChart x g y := by
  unfold partialZBarManifoldAtChart
  have h_distrib :
      ((f - g) : X → ℂ) ∘ (chartAt ℂ x).symm
        = (f ∘ (chartAt ℂ x).symm) - (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h_distrib]
  exact partialZBar_sub hf hg

/-! ## Finset-sum distributivity (mirrors `PartialZBarManifoldFinsetSum`) -/

/-- **Chart-anchored `∂̄` distributes over a finite sum** (under
per-summand `ℝ`-differentiability of the **chart-`x`** pullback at
`(chartAt ℂ x) y`). Proof by `Finset.induction_on`: base case is
`partialZBarManifoldAtChart_zero`; inductive step uses
`partialZBarManifoldAtChart_add` plus the definitional distributivity
`(f + g) ∘ chart.symm = f ∘ chart.symm + g ∘ chart.symm`. -/
theorem partialZBarManifoldAtChart_finset_sum
    {ι : Type*} {x y : X} {t : Finset ι} {f : ι → X → ℂ}
    (h : ∀ i ∈ t,
      DifferentiableAt ℝ (f i ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) :
    partialZBarManifoldAtChart x (fun z => ∑ i ∈ t, f i z) y
      = ∑ i ∈ t, partialZBarManifoldAtChart x (f i) y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert j s hj IH =>
      have h_j : DifferentiableAt ℝ (f j ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) y) := h j (Finset.mem_insert_self j s)
      have h_rest : ∀ i ∈ s,
          DifferentiableAt ℝ (f i ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) y) := fun i hi =>
        h i (Finset.mem_insert.mpr (Or.inr hi))
      have h_sum_rest : DifferentiableAt ℝ
          ((fun z => ∑ i ∈ s, f i z) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) y) := by
        have h_eq : (fun z => ∑ i ∈ s, f i z) ∘ (chartAt ℂ x).symm
            = fun ζ => ∑ i ∈ s, (f i ∘ (chartAt ℂ x).symm) ζ := by
          funext ζ
          rfl
        rw [h_eq]
        exact DifferentiableAt.fun_sum (fun i hi => h_rest i hi)
      have h_lhs_rewrite :
          (fun z : X => ∑ i ∈ insert j s, f i z)
            = f j + (fun z : X => ∑ i ∈ s, f i z) := by
        funext z
        rw [Finset.sum_insert hj]
        rfl
      rw [h_lhs_rewrite, partialZBarManifoldAtChart_add h_j h_sum_rest,
          IH h_rest, Finset.sum_insert hj]

/-! ## Transfer to the chart-at-y `partialZBarManifold` -/

/-- **Transfer lemma — chart-anchored `∂̄` to chart-at-y `∂̄`.**
For `y ∈ (chartAt ℂ x).source` and `f` whose **chart-at-y** pullback
is `ℝ`-differentiable at `(chartAt ℂ y) y`,

```
partialZBarManifoldAtChart x f y
  = partialZBarManifold f y
    * conj(deriv (chartAt ℂ y ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)).
```

This is a re-export of Chip 4's content-agnostic bridge
`partialZBar_chart_x_eq_manifold_mul_transition`, with the LHS folded
into the chart-anchored operator. The hypothesis
`[IsManifold (𝓘(ℂ, ℂ)) ω X]` ensures that chart transitions are ℂ-
analytic at every point of overlap, so the chain-rule application
underlying the bridge has the necessary holomorphy. -/
theorem partialZBarManifoldAtChart_eq_manifold_mul_transition
    [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    {f : X → ℂ} {x y : X}
    (h_y_in : y ∈ (chartAt ℂ x).source)
    (h_f_diff_y : DifferentiableAt ℝ (f ∘ (chartAt ℂ y).symm)
                    ((chartAt ℂ y) y)) :
    partialZBarManifoldAtChart x f y
      = partialZBarManifold f y *
          (starRingEnd ℂ)
            (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)) := by
  -- The LHS unfolds to the LHS of the Chip 4 bridge by definition.
  show partialZBar (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y)
      = partialZBarManifold f y *
          (starRingEnd ℂ)
            (deriv ((chartAt ℂ y) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y))
  exact JacobianChallenge.PompeiuKernel.partialZBar_chart_x_eq_manifold_mul_transition
    (f := f) (x := x) (y := y) h_y_in h_f_diff_y

end JacobianChallenge

end
