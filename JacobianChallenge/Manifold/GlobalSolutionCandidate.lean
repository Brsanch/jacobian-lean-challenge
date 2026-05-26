/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionAtBasepoint
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-! # The global solution candidate `Σ_i v_i`

Given a chart cover `cover`, partition `P`, source α, and a choice of
chart-source cutoffs `χs` (one per base point), the **global solution
candidate** is

```
globalSolutionCandidate P α χs y := ∑ i, localPompeiuSolutionGlobal P i α (χs i) y
```

summed over the finite set of base points (a `Fintype` derived from
`cover.basePoints : Finset X`).

This is the candidate for the global `∂̄`-inverse `u : X → ℂ`
satisfying `∂̄_man u = α` on supp(P.rhoC i) ⊂ chart_xi.source for each
i. The Sub-chip 5.6 manifold identity will combine this with the
per-i recovery identity
(`partialZBarManifold_localPompeiuSolutionGlobal_eq_α_mul_transition_on_support_rhoC`)
to derive a partition-of-unity equation modulo the chart-transition
factor sum.

## Main definitions / results

* `globalSolutionCandidate` — the finite sum.
* `contMDiff_globalSolutionCandidate` — global smoothness via
  `contMDiff_finset_sum`.

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

/-- The **global solution candidate**: sum of the per-i local Pompeiu
solutions over the finite set of base points. -/
def globalSolutionCandidate
    (P : FiniteChartCoverPartition cover)
    (α : X → ℂ)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i) : X → ℂ :=
  fun y => ∑ i : {x : X // x ∈ cover.basePoints},
    localPompeiuSolutionGlobal P i α (χs i) y

/-- **Global smoothness.** The finite sum of `ContMDiff` functions is
`ContMDiff` (via `contMDiff_finset_sum` plus the
`ContMDiffAdd 𝓘(ℝ, ℂ) ∞ ℂ` instance from the
`contMDiffRing_complex_over_real` registered in Sub-chip 5.3c). -/
theorem contMDiff_globalSolutionCandidate
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (globalSolutionCandidate P α χs) := by
  classical
  -- Each summand is ContMDiff (Sub-chip 5.4b).
  have h_each : ∀ i : {x : X // x ∈ cover.basePoints},
      ∀ _ : i ∈ Finset.univ,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (localPompeiuSolutionGlobal P i α (χs i)) := by
    intro i _
    exact contMDiff_localPompeiuSolutionGlobal P i α h_α (χs i)
  -- Apply the finset-sum version.
  exact contMDiff_finset_sum (t := (Finset.univ : Finset _)) h_each

end JacobianChallenge

end
