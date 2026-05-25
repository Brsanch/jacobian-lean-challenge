/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartPompeiuSolutionManifoldIdentity

/-! # Combined per-i identity for `v_i`

Closes the Sub-chip 5.4 trilogy with a single clean statement:

```
partialZBarManifold (localPompeiuSolutionGlobal P i α χ) y *
    conj(deriv (chartAt ℂ y ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y))
  = (P.rhoC i * α) y
```

for every `y ∈ support (P.rhoC i)`. The composition of:

* Sub-chip 5.4c-prep
  (`partialZBarManifold_localPompeiuSolutionGlobal_eq_chartPompeiuSolution_on_support_rhoC`)
  — `∂̄_man v_i = ∂̄_man (chartPompeiuSolution)` on `support (P.rhoC i)`
  (cutoff peel-off via local-coincidence + germ-dependence), and

* Sub-chip 5.4c-final
  (`partialZBarManifold_chartPompeiuSolution_eq_α_mul_transition`)
  — the chart-transition factor identity for `chartPompeiuSolution`.

The auxiliary inclusion `support (P.rhoC i) ⊆ (chartAt ℂ i.val).source`
follows from `subset_tsupport` plus Sub-chip 5.2's `tsupport_rhoC_subset`.

This single identity is the **per-i recovery** that Sub-chip 5.5
(Behnke-Stein spreading) will combine into a global `∂̄`-solution
candidate via the partition-of-unity sum.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {cover : FiniteChartCover X}

/-- `support (P.rhoC i) ⊆ (chartAt ℂ i.val).source` (via `subset_tsupport` +
Sub-chip 5.2's `tsupport_rhoC_subset`). -/
theorem support_rhoC_subset_chart_source
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) :
    Function.support (P.rhoC i) ⊆ (chartAt ℂ i.val).source :=
  (subset_tsupport _).trans (P.tsupport_rhoC_subset i)

/-- **Per-i recovery identity.** On `support (P.rhoC i)`, the
manifold-side `∂̄` of `v_i` multiplied by the chart-transition factor
recovers `(P.rhoC i * α) y`. Composition of Sub-chip 5.4c-prep and
Sub-chip 5.4c-final, with `support (P.rhoC i) ⊆ chart_xi.source`
supplied by `support_rhoC_subset_chart_source`. -/
theorem partialZBarManifold_localPompeiuSolutionGlobal_eq_α_mul_transition_on_support_rhoC
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∈ Function.support (P.rhoC i)) :
    JacobianChallenge.partialZBarManifold
        (localPompeiuSolutionGlobal P i α χ) y *
      (starRingEnd ℂ)
        (deriv ((chartAt ℂ y) ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y))
      = (P.rhoC i * α) y := by
  -- Sub-chip 5.4c-prep: ∂̄_man v_i = ∂̄_man (chartPompeiuSolution) on support.
  rw [partialZBarManifold_localPompeiuSolutionGlobal_eq_chartPompeiuSolution_on_support_rhoC
        P i α χ hy]
  -- Sub-chip 5.4c-final: the chart-transition identity for chartPompeiuSolution.
  -- Need y ∈ chart_xi.source, supplied by the support inclusion.
  exact partialZBarManifold_chartPompeiuSolution_eq_α_mul_transition
    P i α h_α (support_rhoC_subset_chart_source P i hy)

end JacobianChallenge

end
