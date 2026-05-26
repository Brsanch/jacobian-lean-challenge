/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBarManifold
import Mathlib.Algebra.BigOperators.Pi

/-! # `partialZBarManifold` is `ℝ`-linear over finite sums

The manifold-side antiholomorphic Wirtinger derivative
`partialZBarManifold : (X → ℂ) → X → ℂ` distributes over finite sums
(under the per-summand differentiability hypothesis on the chart
pullback). This is the bridge from per-i identities to the sum
identity needed by Sub-chip 5.6 (the final manifold identity).

The proof is `Finset.induction_on`: base case is `partialZBarManifold_zero`,
inductive step uses `partialZBarManifold_add` plus the fact that the
chart pullback distributes over the sum.

The differentiability hypothesis is per-summand on the chart-pullback
`f i ∘ extChartAt.symm` at `extChartAt x`.

## Main result

* `partialZBarManifold_finset_sum` — `partialZBarManifold (Σ_{i ∈ t} f i) x
  = Σ_{i ∈ t} partialZBarManifold (f i) x`.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Manifold-side `∂̄` distributes over a finite sum** (under per-
summand differentiability of the chart pullback). Proof by Finset
induction: base case `partialZBarManifold_zero`; inductive step uses
`partialZBarManifold_add` plus the fact that `(f + g) ∘ chart.symm =
f ∘ chart.symm + g ∘ chart.symm` (i.e. the chart pullback is
distributive over `+`, which follows definitionally for ℂ-valued
functions). -/
theorem partialZBarManifold_finset_sum
    {ι : Type*} {x : X} {t : Finset ι} {f : ι → X → ℂ}
    (h : ∀ i ∈ t,
      DifferentiableAt ℝ (f i ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
        ((extChartAt 𝓘(ℂ, ℂ) x) x)) :
    partialZBarManifold (fun y => ∑ i ∈ t, f i y) x
      = ∑ i ∈ t, partialZBarManifold (f i) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [partialZBarManifold_zero]
  | insert j s hj IH =>
      -- Split the hypothesis.
      have h_j : DifferentiableAt ℝ (f j ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          ((extChartAt 𝓘(ℂ, ℂ) x) x) := h j (Finset.mem_insert_self j s)
      have h_rest : ∀ i ∈ s,
          DifferentiableAt ℝ (f i ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
            ((extChartAt 𝓘(ℂ, ℂ) x) x) := fun i hi =>
        h i (Finset.mem_insert.mpr (Or.inr hi))
      -- Recursive sum is differentiable.
      have h_sum_rest : DifferentiableAt ℝ
          ((fun y => ∑ i ∈ s, f i y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
          ((extChartAt 𝓘(ℂ, ℂ) x) x) := by
        have h_eq : (fun y => ∑ i ∈ s, f i y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
            = fun ζ => ∑ i ∈ s, (f i ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ζ := by
          funext ζ
          rfl
        rw [h_eq]
        exact DifferentiableAt.fun_sum (fun i hi => h_rest i hi)
      -- Apply Finset.sum_insert pointwise inside the lambda on the LHS,
      -- then partialZBarManifold_add, then IH.
      have h_lhs_rewrite :
          (fun y : X => ∑ i ∈ insert j s, f i y)
            = f j + (fun y : X => ∑ i ∈ s, f i y) := by
        funext y
        rw [Finset.sum_insert hj]
        rfl
      rw [h_lhs_rewrite, partialZBarManifold_add h_j h_sum_rest,
          IH h_rest, Finset.sum_insert hj]

end JacobianChallenge

end
