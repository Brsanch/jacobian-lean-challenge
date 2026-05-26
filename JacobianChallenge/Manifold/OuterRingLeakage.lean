/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionLeibnizChartConst
import JacobianChallenge.Manifold.PartialZBarManifoldLocalPompeiuChartConst
import JacobianChallenge.Manifold.LocalPompeiuSolutionGlobalZeroOffTsupport
import JacobianChallenge.Manifold.GlobalSolutionCandidatePartialZBar
import JacobianChallenge.Manifold.PartitionSumMulAlpha

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-h — explicit outer-ring leakage form

Sub-chip 5.5c-I-e shipped the **conditional** global identity
`partialZBarManifold u y = α y` under global chart-const + a
per-call outer-ring-vanish hypothesis. This sub-chip makes that
hypothesis **explicit** as a sum:

```
partialZBarManifold (globalSolutionCandidate P α χs) y
  = α y + outerRingLeakage P α χs y
```

where

```
outerRingLeakage P α χs y :=
  ∑ i, if (y ∈ tsupport (χs i).toFun ∧ y ∉ Function.support (P.rhoC i))
       then partialZBarManifold ((χs i).toFun · : X → ℂ) y *
              pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                ((chartAt ℂ i.val) y)
       else 0.
```

This is the EXPLICIT analytic content blocking the
`DBarSolvabilityAtGenusZero X` discharge from the partition-Pompeiu
candidate: the cutoff-derivative-times-Pompeiu-kernel sum on the
outer rings of the χ_i. A future cancellation argument, Behnke-Stein
iteration, or specific construction of the χ_i making this sum
vanish would close `partialZBarManifold u y = α y` immediately.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff Classical
open Set Function
open JacobianChallenge.PompeiuKernel

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
  {cover : FiniteChartCover X}

/-- The **per-i outer-ring leakage** at `y`: the cutoff-derivative-
times-Pompeiu-kernel term that contributes to
`partialZBarManifold v_i y` on the outer ring
`tsupport (χs i).toFun \ Function.support (P.rhoC i)`, and zero
elsewhere. -/
def outerRingLeakageAt
    (P : FiniteChartCoverPartition cover)
    (α : X → ℂ)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (i : {x : X // x ∈ cover.basePoints}) (y : X) : ℂ :=
  if y ∈ tsupport (χs i).toFun ∧ y ∉ Function.support (P.rhoC i) then
    partialZBarManifold (fun z : X => (((χs i).toFun z : ℝ) : ℂ)) y *
      pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
        ((chartAt ℂ i.val) y)
  else 0

/-- The **outer-ring leakage** at `y` is the finite sum of per-i
outer-ring contributions. -/
def outerRingLeakage
    (P : FiniteChartCoverPartition cover)
    (α : X → ℂ)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) : ℂ :=
  ∑ i : {x : X // x ∈ cover.basePoints}, outerRingLeakageAt P α χs i y

/-- **Per-`i` identity decomposing `partialZBarManifold v_i y` into
the partition-times-α term plus the outer-ring leakage.** Under
global chart-const, for every `i` and every `y : X`:
```
partialZBarManifold v_i y = (P.rhoC i * α) y + outerRingLeakageAt P α χs i y.
```
Case-split on `y ∈ tsupport (χs i).toFun` and `y ∈ support (P.rhoC i)`.
-/
private lemma per_i_identity_with_leakage
    (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y
      = (P.rhoC i * α) y + outerRingLeakageAt P α χs i y := by
  by_cases h_supp : y ∈ Function.support (P.rhoC i)
  · -- Case A: y ∈ support(ρ_i). LHS = (ρ_i α)(y) by 5.5c-I-d; leakage = 0.
    have h_lhs :
        partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y
          = (P.rhoC i * α) y :=
      partialZBarManifold_localPompeiuSolutionGlobal_eq_rhoC_mul_alpha_under_chart_const
        P i h_α (χs i) h_chart h_supp
    have h_leak_zero : outerRingLeakageAt P α χs i y = 0 := by
      unfold outerRingLeakageAt
      rw [if_neg]
      exact fun ⟨_, h_not_supp⟩ => h_not_supp h_supp
    rw [h_lhs, h_leak_zero, add_zero]
  · -- Case B: y ∉ support(ρ_i). RHS's first term is 0.
    have h_rhoC_zero : P.rhoC i y = 0 := Function.notMem_support.mp h_supp
    have h_rhs_first : (P.rhoC i * α) y = 0 := by
      show P.rhoC i y * α y = 0
      rw [h_rhoC_zero, zero_mul]
    by_cases h_tchi : y ∈ tsupport (χs i).toFun
    · -- B.1: y ∈ outer ring. LHS = leakage via 5.5c-I-g.
      -- y ∈ chart_{i.val}.source (since outer ring ⊆ tsupport χ ⊆ chart_{i.val}.source).
      have h_y_src : y ∈ (chartAt ℂ i.val).source := (χs i).tsupport_subset h_tchi
      have h_leibniz :=
        partialZBarManifold_localPompeiuSolutionGlobal_leibniz_under_chart_const
          P i h_α (χs i) h_chart h_y_src
      -- The second term in the Leibniz identity is χ y * (ρ_i α) y = χ y * 0 = 0.
      have h_second_zero :
          ((((χs i).toFun y : ℝ)) : ℂ) * (P.rhoC i * α) y = 0 := by
        rw [h_rhs_first, mul_zero]
      rw [h_second_zero, add_zero] at h_leibniz
      -- Now h_leibniz says: partialZBarManifold v_i y =
      --                     partialZBarManifold (χcast) y · K_i(chart_{i.val} y).
      -- RHS leakage in this case: same expression (outer-ring `if` triggers).
      have h_leak :
          outerRingLeakageAt P α χs i y
            = partialZBarManifold (fun z : X => (((χs i).toFun z : ℝ) : ℂ)) y *
                pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                  ((chartAt ℂ i.val) y) := by
        unfold outerRingLeakageAt
        rw [if_pos ⟨h_tchi, h_supp⟩]
      rw [h_rhs_first, zero_add, h_leak]
      exact h_leibniz
    · -- B.2: y ∉ tsupport(χ_i). LHS = 0 (trivial vanishing). Leakage = 0.
      have h_lhs_zero :
          partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y = 0 :=
        partialZBarManifold_localPompeiuSolutionGlobal_eq_zero_off_tsupport_chi
          P i α (χs i) h_tchi
      have h_leak_zero : outerRingLeakageAt P α χs i y = 0 := by
        unfold outerRingLeakageAt
        rw [if_neg]
        exact fun ⟨h_tchi', _⟩ => h_tchi h_tchi'
      rw [h_lhs_zero, h_rhs_first, h_leak_zero, zero_add]

/-- **The explicit-leakage global identity.** Under global chart-const,

```
partialZBarManifold (globalSolutionCandidate P α χs) y
  = α y + outerRingLeakage P α χs y.
```

The right-hand side makes the genuine analytic content (the
cutoff-derivative-times-Pompeiu-kernel sum on the outer rings)
fully explicit. Closing
`DBarSolvabilityAtGenusZero X` from the partition-Pompeiu candidate
amounts to proving `outerRingLeakage P α χs y = 0` for all `y`. -/
theorem partialZBarManifold_globalSolutionCandidate_eq_α_add_outerRingLeakage
    (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    (y : X) :
    partialZBarManifold (globalSolutionCandidate P α χs) y
      = α y + outerRingLeakage P α χs y := by
  -- Assembly distributivity.
  rw [partialZBarManifold_globalSolutionCandidate_eq_finset_sum P α h_α χs y]
  -- Rewrite each summand via the per-i identity.
  have h_per_i :
      ∀ i ∈ (Finset.univ : Finset {x : X // x ∈ cover.basePoints}),
        partialZBarManifold (localPompeiuSolutionGlobal P i α (χs i)) y
          = (P.rhoC i * α) y + outerRingLeakageAt P α χs i y :=
    fun i _ => per_i_identity_with_leakage P h_α χs h_chart i y
  rw [Finset.sum_congr rfl h_per_i]
  -- Split the sum into partition contribution + leakage.
  rw [Finset.sum_add_distrib]
  -- Partition contribution sums to α y; leakage is the named outerRingLeakage.
  rw [sum_rhoC_mul_α_eq_α P α y]
  rfl

/-- **Closure-by-outer-ring-vanish corollary.** If the explicit
leakage `outerRingLeakage P α χs y = 0`, then
`partialZBarManifold u y = α y`. The remaining content of any future
closure is `outerRingLeakage = 0` — a concrete computational
statement, not a new named Prop. -/
theorem partialZBarManifold_globalSolutionCandidate_eq_α_of_outerRing_zero
    (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    (y : X) (h_zero : outerRingLeakage P α χs y = 0) :
    partialZBarManifold (globalSolutionCandidate P α χs) y = α y := by
  rw [partialZBarManifold_globalSolutionCandidate_eq_α_add_outerRingLeakage
    P h_α χs h_chart y, h_zero, add_zero]

end JacobianChallenge

end
