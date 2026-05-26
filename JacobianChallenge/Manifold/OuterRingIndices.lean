/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.OuterRingLeakage

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-i — filtered-Finset form of the outer-ring leakage

Sub-chip 5.5c-I-h defined `outerRingLeakage` via an `if`-`then`-`else`
inside a `Finset.sum`. This sub-chip rewrites it as a sum over a
**filtered Finset** of outer-ring indices, exposing the genuine
analytic content as a clean sum and providing characterization
lemmas that downstream cancellation / iteration arguments will need.

## What this file ships

* `outerRingIndices P χs y : Finset {x // x ∈ cover.basePoints}` —
  the indices `i` for which `y ∈ tsupport (χs i).toFun \
  Function.support (P.rhoC i)`.
* `mem_outerRingIndices_iff` — characterization of membership.
* `outerRingLeakage_eq_sum_over_outerRingIndices` — the headline
  identity:
  ```
  outerRingLeakage P α χs y =
    ∑ i ∈ outerRingIndices P χs y,
      partialZBarManifold ((χs i).toFun · : X → ℂ) y *
        pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
          ((chartAt ℂ i.val) y).
  ```
* `notMem_outerRingIndices_of_mem_support_rhoC` — if
  `y ∈ Function.support (P.rhoC i)`, then `i ∉ outerRingIndices y`.
* `outerRingLeakageAt_eq_zero_on_support_rhoC` — the per-`i`
  vanishing on partition support (the `i`-term contributes zero
  to the leakage at any `y` where `ρ_i(y) ≠ 0`).

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

/-- The **outer-ring index set** at `y`: indices `i` for which
`y ∈ tsupport (χs i).toFun` and `y ∉ Function.support (P.rhoC i)`. -/
def outerRingIndices
    (P : FiniteChartCoverPartition cover)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) : Finset {x : X // x ∈ cover.basePoints} :=
  (Finset.univ : Finset {x : X // x ∈ cover.basePoints}).filter
    (fun i => y ∈ tsupport (χs i).toFun ∧ y ∉ Function.support (P.rhoC i))

/-- Membership in `outerRingIndices y` is the conjunction of the
two outer-ring conditions. -/
@[simp] lemma mem_outerRingIndices_iff
    (P : FiniteChartCoverPartition cover)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) (i : {x : X // x ∈ cover.basePoints}) :
    i ∈ outerRingIndices P χs y ↔
      y ∈ tsupport (χs i).toFun ∧ y ∉ Function.support (P.rhoC i) := by
  unfold outerRingIndices
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ i)

/-- `i ∉ outerRingIndices y` whenever `y ∈ Function.support (P.rhoC i)`. -/
lemma notMem_outerRingIndices_of_mem_support_rhoC
    (P : FiniteChartCoverPartition cover)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    {i : {x : X // x ∈ cover.basePoints}} {y : X}
    (h : y ∈ Function.support (P.rhoC i)) :
    i ∉ outerRingIndices P χs y := by
  rw [mem_outerRingIndices_iff]
  intro ⟨_, h_not_supp⟩
  exact h_not_supp h

/-- The per-`i` leakage `outerRingLeakageAt` is zero at any `y` in
`Function.support (P.rhoC i)`. -/
lemma outerRingLeakageAt_eq_zero_on_support_rhoC
    (P : FiniteChartCoverPartition cover) (α : X → ℂ)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    {i : {x : X // x ∈ cover.basePoints}} {y : X}
    (h : y ∈ Function.support (P.rhoC i)) :
    outerRingLeakageAt P α χs i y = 0 := by
  unfold outerRingLeakageAt
  rw [if_neg]
  rintro ⟨_, h_not_supp⟩
  exact h_not_supp h

/-- The per-`i` leakage `outerRingLeakageAt` is zero whenever
`y ∉ tsupport (χs i).toFun`. -/
lemma outerRingLeakageAt_eq_zero_off_tsupport
    (P : FiniteChartCoverPartition cover) (α : X → ℂ)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    {i : {x : X // x ∈ cover.basePoints}} {y : X}
    (h : y ∉ tsupport (χs i).toFun) :
    outerRingLeakageAt P α χs i y = 0 := by
  unfold outerRingLeakageAt
  rw [if_neg]
  rintro ⟨h_tchi, _⟩
  exact h h_tchi

/-- **The filtered-Finset form of the outer-ring leakage.** Sums only
over the outer-ring indices; the value on each is the
cutoff-derivative-times-Pompeiu-kernel term, with the `if`-`then`-`else`
discharged by the filter condition. -/
theorem outerRingLeakage_eq_sum_over_outerRingIndices
    (P : FiniteChartCoverPartition cover) (α : X → ℂ)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) :
    outerRingLeakage P α χs y =
      ∑ i ∈ outerRingIndices P χs y,
        partialZBarManifold (fun z : X => (((χs i).toFun z : ℝ) : ℂ)) y *
          pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
            ((chartAt ℂ i.val) y) := by
  unfold outerRingLeakage outerRingIndices outerRingLeakageAt
  -- Rewrite the sum over `Finset.univ` with `if-then-else` as a
  -- sum over the filtered Finset.
  rw [← Finset.sum_filter]

/-- Specialization: at any `y ∈ Function.support (P.rhoC i)`, the
`i`-th index does NOT contribute to the outer-ring leakage sum. The
leakage at `y` is contributed by OTHER indices' outer rings only. -/
lemma outerRingIndices_subset_compl_support_rhoC
    (P : FiniteChartCoverPartition cover)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) :
    ∀ i ∈ outerRingIndices P χs y, y ∉ Function.support (P.rhoC i) := by
  intro i hi
  rw [mem_outerRingIndices_iff] at hi
  exact hi.2

/-- Specialization: every index in `outerRingIndices y` has `y` in
its cutoff's `tsupport`. -/
lemma outerRingIndices_subset_tsupport_chi
    (P : FiniteChartCoverPartition cover)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) :
    ∀ i ∈ outerRingIndices P χs y, y ∈ tsupport (χs i).toFun := by
  intro i hi
  rw [mem_outerRingIndices_iff] at hi
  exact hi.1

/-- Specialization: every index in `outerRingIndices y` has
`y ∈ (chartAt ℂ i.val).source` (since `tsupport (χs i).toFun ⊆
(chartAt ℂ i.val).source` by Sub-chip 5.4a). -/
lemma outerRingIndices_subset_chart_source
    (P : FiniteChartCoverPartition cover)
    (χs : ∀ i : {x : X // x ∈ cover.basePoints},
      PartitionChartSourceCutoff P i)
    (y : X) :
    ∀ i ∈ outerRingIndices P χs y, y ∈ (chartAt ℂ i.val).source := by
  intro i hi
  exact (χs i).tsupport_subset (outerRingIndices_subset_tsupport_chi P χs y i hi)

end JacobianChallenge

end
