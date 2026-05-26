/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartialZBarManifoldLocalPompeiuChartConst
import JacobianChallenge.Manifold.LocalPompeiuSolutionGlobalZeroOffTsupport
import JacobianChallenge.Manifold.PartitionSumMulAlpha

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-e — global assembly under chart-const

Composes the per-`i` recovery from Sub-chip 5.5c-I-d, the trivial-
vanishing-off-`tsupport χ_i` case from the assembly layer, and the
assembly distributivity
`partialZBarManifold_globalSolutionCandidate_eq_finset_sum`, to give
the **conditional global identity**

```
partialZBarManifold (globalSolutionCandidate P α χs) y = α y
```

under

1. The global chart-locality hypothesis `∀ p, ChartAtConstantOnSource p`.
2. An **outer-ring-vanishing hypothesis**: for every `i` such that
   `y ∈ tsupport (χs i).toFun \ Function.support (P.rhoC i)` (the
   "outer ring" of the cutoff `χ_i`, where the smooth cutoff has not
   yet reached zero but the partition `ρ_i` has),
   `partialZBarManifold (v_i) y = 0`.

The outer-ring-vanishing hypothesis is the **genuine analytic
obstacle** to closing `DBarSolvabilityAtGenusZero X` from the
partition-Pompeiu candidate alone: the cutoff `χ_i` contributes
`(∂̄ χ_i ∘ chart_{i.val}.symm)(z) · K_i(z)` on the outer ring, which
does not generally cancel across `i`. This sub-chip ships the
conditional, identifying the outer-ring leakage as the precise
remaining obstruction, **without** introducing a new named `Prop`
(the outer-ring hypothesis is taken inline per-call, not as a
project-wide named hypothesis).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Function

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
  {cover : FiniteChartCover X}

/-- **Per-`i` unified identity (under chart-const + outer-ring vanish).**
For every `y : X` and every `i : {x // x ∈ cover.basePoints}`, under
global chart-const and outer-ring vanish at `y`:

```
partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y
  = (P.rhoC i * α) y.
```

Case split: `y ∈ support (P.rhoC i)` ⟹ 5.5c-I-d. Otherwise both sides
are zero — LHS by trivial-vanishing (off `tsupport χ_i`) or
outer-ring hypothesis (on outer ring); RHS because `(P.rhoC i)(y) = 0`
when `y` is not in the open support, hence `(P.rhoC i * α)(y) = 0`. -/
private lemma per_i_identity_under_chart_const_and_outer_vanish
    (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    {y : X}
    (h_outer_vanish : ∀ i : {x : X // x ∈ cover.basePoints},
      y ∈ tsupport (χs i).toFun \ Function.support (P.rhoC i) →
      partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y = 0)
    (i : {x : X // x ∈ cover.basePoints}) :
    partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y
      = (P.rhoC i * α) y := by
  by_cases h_supp : y ∈ Function.support (P.rhoC i)
  · -- Case A: y in the open support — Sub-chip 5.5c-I-d.
    exact partialZBarManifold_localPompeiuSolutionGlobal_eq_rhoC_mul_alpha_under_chart_const
      P i h_α (χs i) h_chart h_supp
  · -- Case B: y outside the support. (P.rhoC i)(y) = 0 ⟹ RHS = 0.
    have h_rhoC_zero : P.rhoC i y = 0 := Function.notMem_support.mp h_supp
    have h_rhs_zero : (P.rhoC i * α) y = 0 := by
      show P.rhoC i y * α y = 0
      rw [h_rhoC_zero, zero_mul]
    -- LHS = 0 via either trivial-vanishing or outer-ring vanish.
    by_cases h_tchi : y ∈ tsupport (χs i).toFun
    · -- y ∈ outer ring of χ_i (in tsupport χ_i but not in support ρ_i).
      have h_outer_mem : y ∈ tsupport (χs i).toFun \ Function.support (P.rhoC i) :=
        ⟨h_tchi, h_supp⟩
      rw [h_outer_vanish i h_outer_mem, h_rhs_zero]
    · -- y ∉ tsupport χ_i ⟹ trivial vanishing (assembly layer).
      rw [partialZBarManifold_localPompeiuSolutionGlobal_eq_zero_off_tsupport_chi
        P i α (χs i) h_tchi, h_rhs_zero]

/-- **Conditional global identity** for the partition-Pompeiu candidate
under chart-const + outer-ring vanish. The remaining analytic content
(outer-ring leakage cancellation) is made explicit as a per-call
hypothesis. -/
theorem partialZBarManifold_globalSolutionCandidate_eq_α_under_chart_const_and_outer_vanish
    (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    (y : X)
    (h_outer_vanish : ∀ i : {x : X // x ∈ cover.basePoints},
      y ∈ tsupport (χs i).toFun \ Function.support (P.rhoC i) →
      partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y = 0) :
    partialZBarManifold (globalSolutionCandidate P α χs) y = α y := by
  -- Assembly distributivity (already in tree).
  rw [partialZBarManifold_globalSolutionCandidate_eq_finset_sum P α h_α χs y]
  -- Replace each summand by (P.rhoC i * α)(y) via the per-i identity.
  have h_per_i :
      ∀ i ∈ (Finset.univ : Finset {x : X // x ∈ cover.basePoints}),
        partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y
          = (P.rhoC i * α) y :=
    fun i _ =>
      per_i_identity_under_chart_const_and_outer_vanish P h_α χs h_chart
        h_outer_vanish i
  rw [Finset.sum_congr rfl h_per_i]
  -- Partition-of-unity identity.
  exact sum_rhoC_mul_α_eq_α P α y

end JacobianChallenge

end
