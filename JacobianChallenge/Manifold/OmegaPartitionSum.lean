/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.OmegaFormOfChartLocalConstructor
import JacobianChallenge.Manifold.PartitionOfUnitySubordinateToCover
import JacobianChallenge.Manifold.PartitionSumMulAlpha
import JacobianChallenge.Manifold.LocalPompeiuSolutionChart
import JacobianChallenge.Manifold.ForsterCutoffPoleConstruction

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-c — partition sum at the `OmegaForm` level

Given a smooth partition of unity `P` subordinate to a finite chart
cover, and any smooth `α : X → ℂ`, builds the `(0,1)`-form

```
ω_α := ∑_i OmegaForm.ofChartLocalFunction i.val (P.rhoC i * α) …
```

and proves the **canonical-chart recovery**

```
ω_α.coeff y ((chartAt ℂ y) y) = α y
```

under the global hypothesis that `chartAt ℂ` is locally constant on
every chart's source (`∀ p, ChartAtConstantOnSource p`). This is the
same per-point hypothesis the Forster §16.9 cutoff already takes,
extended to the whole atlas; it holds on every concrete `X` whose
charted-space structure assigns a single canonical chart to each
region.

## Method

Per `i`:

* **`y ∈ chart_{i.val}.source`** (the relevant case): under
  `ChartAtConstantOnSource i.val`, `chartAt ℂ y = chartAt ℂ i.val`, so
  the transition derivative `deriv (chart_y ∘ chart_{i.val}.symm)` at
  `chart_{i.val}(y)` equals `deriv id = 1` (the composition agrees
  with `id` on the open neighborhood `chart_{i.val}.target` of
  `chart_{i.val}(y)`). The `localFormCoeff` cocycle factor collapses
  to `conj 1 = 1`, leaving `(P.rhoC i * α)(y)`.

* **`y ∉ chart_{i.val}.source`**: then `y ∉ tsupport (P.rhoC i)` (by
  `P.tsupport_rhoC_subset`), so `(P.rhoC i)(y) = 0` and
  `(P.rhoC i * α)(y) = 0`. Also `y ∉ tsupport (P.rhoC i * α)`, so
  `localFormCoeff i.val (P.rhoC i * α) y _ = 0` via
  `localFormCoeff_eq_zero_of_not_mem_tsupport`.

Summing per `i`, the partition-of-unity identity
`P.sum_rhoC_mul_α_eq_α` (Sub-chip 5.4-assembly's
`PartitionSumMulAlpha`) collapses the sum to `α y`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff Classical
open Set Function

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

namespace OmegaForm

/-! ## Auxiliary support / smoothness for `P.rhoC i * α` -/

/-- `tsupport (P.rhoC i * α) ⊆ tsupport (P.rhoC i) ⊆ chart_{i.val}.source`. -/
lemma tsupport_rhoCmul_subset_chart_source
    {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ) :
    tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source := by
  refine subset_trans ?_ (P.tsupport_rhoC_subset i)
  exact closure_mono (Function.support_mul_subset_left _ _)

/-- `P.rhoC i * α` is `ContMDiff` whenever `α` is. -/
lemma rhoCmul_contMDiff
    {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) {α : X → ℂ}
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
  (P.rhoC_smooth i).mul h_α

/-! ## The partition sum as a `Finset.sum` at the form level -/

/-- The `(0,1)`-form partition sum
`ω_α := ∑_i OmegaForm.ofChartLocalFunction i.val (P.rhoC i * α)`. -/
def omegaPartitionSum
    {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) :
    OmegaForm X :=
  ∑ i : {x : X // x ∈ cover.basePoints},
    ofChartLocalFunction i.val (P.rhoC i * α)
      (rhoCmul_contMDiff P i h_α)
      (tsupport_rhoCmul_subset_chart_source P i α)

/-- Evaluation `f ↦ f.coeff y z` as an `AddMonoidHom`. Used to push
`Finset.sum` through the `coeff` field. -/
def evalCoeffHom (y : X) (z : ℂ) : OmegaForm X →+ ℂ where
  toFun f := f.coeff y z
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] lemma evalCoeffHom_apply (f : OmegaForm X) (y : X) (z : ℂ) :
    evalCoeffHom y z f = f.coeff y z := rfl

/-- The `coeff` of the partition sum is the pointwise sum of the per-`i`
`localFormCoeff`s. -/
lemma omegaPartitionSum_coeff
    {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) (y : X) (z : ℂ) :
    (omegaPartitionSum P h_α).coeff y z
      = ∑ i : {x : X // x ∈ cover.basePoints},
          localFormCoeff i.val (P.rhoC i * α) y z := by
  unfold omegaPartitionSum
  rw [← evalCoeffHom_apply (y := y) (z := z), map_sum]
  rfl

/-! ## Per-`i` canonical-chart recovery -/

/-- **Per-`i` recovery under global `ChartAtConstantOnSource`.** For
each `i` and each `y : X`,
```
localFormCoeff i.val (P.rhoC i * α) y ((chartAt ℂ y) y) = (P.rhoC i * α) y.
```
Case-split on `y ∈ chart_{i.val}.source`:

* In the source: the chart-locality hypothesis collapses the
  transition derivative to `1`, leaving `(P.rhoC i * α)(y)`.
* Off the source: both sides vanish via `tsupport`-zero arguments.
-/
lemma omegaPartitionSum_per_i_recovery_at_chart_y
    {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
    (α : X → ℂ)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    (i : {x : X // x ∈ cover.basePoints}) (y : X) :
    localFormCoeff i.val (P.rhoC i * α) y ((chartAt ℂ y) y)
      = (P.rhoC i * α) y := by
  by_cases h_mem : y ∈ (chartAt ℂ i.val).source
  · -- Case 1: y in the chart source.
    have h_chart_eq : chartAt ℂ y = chartAt ℂ i.val := h_chart i.val y h_mem
    have h_y_src : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
    have h_symm : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
      (chartAt ℂ y).left_inv h_y_src
    have h_symm_in_src :
        (chartAt ℂ y).symm ((chartAt ℂ y) y) ∈ (chartAt ℂ i.val).source := by
      rw [h_symm]; exact h_mem
    rw [localFormCoeff_of_mem (h := h_symm_in_src), h_symm]
    -- Show deriv(chart_y ∘ chart_{i.val}.symm)(chart_{i.val} y) = 1.
    have h_deriv :
        deriv ((chartAt ℂ y) ∘ (chartAt ℂ i.val).symm) ((chartAt ℂ i.val) y) = 1 := by
      rw [h_chart_eq]
      have h_y_tgt : (chartAt ℂ i.val) y ∈ (chartAt ℂ i.val).target :=
        (chartAt ℂ i.val).map_source h_mem
      have h_open : IsOpen (chartAt ℂ i.val).target := (chartAt ℂ i.val).open_target
      have h_evEq :
          ((chartAt ℂ i.val) ∘ (chartAt ℂ i.val).symm)
            =ᶠ[𝓝 ((chartAt ℂ i.val) y)] id := by
        filter_upwards [h_open.mem_nhds h_y_tgt] with w hw
        show (chartAt ℂ i.val) ((chartAt ℂ i.val).symm w) = w
        exact (chartAt ℂ i.val).right_inv hw
      rw [Filter.EventuallyEq.deriv_eq h_evEq, deriv_id]
    rw [h_deriv, show (starRingEnd ℂ) 1 = 1 from map_one _, div_one]
  · -- Case 2: y outside the chart source.
    -- (P.rhoC i)(y) = 0 since tsupport ⊆ open chart_{i.val}.source.
    have h_not_in_tsupport_rhoC : y ∉ tsupport (P.rhoC i) :=
      fun h => h_mem (P.tsupport_rhoC_subset i h)
    have h_not_in_tsupport_mul : y ∉ tsupport (P.rhoC i * α) := by
      intro h
      apply h_not_in_tsupport_rhoC
      exact closure_mono (Function.support_mul_subset_left _ _) h
    have h_lhs :
        localFormCoeff i.val (P.rhoC i * α) y ((chartAt ℂ y) y) = 0 :=
      localFormCoeff_eq_zero_of_not_mem_tsupport i.val (P.rhoC i * α) y
        (mem_chart_source ℂ y) h_not_in_tsupport_mul
    have h_rhoC_zero : P.rhoC i y = 0 := by
      have h_not_supp : y ∉ Function.support (P.rhoC i) :=
        fun h => h_not_in_tsupport_rhoC (subset_tsupport _ h)
      exact Function.notMem_support.mp h_not_supp
    have h_rhs : (P.rhoC i * α) y = 0 := by
      show P.rhoC i y * α y = 0
      rw [h_rhoC_zero, zero_mul]
    rw [h_lhs, h_rhs]

/-! ## The canonical-chart recovery theorem -/

/-- **Canonical-chart recovery.** Under the global hypothesis
`∀ p, ChartAtConstantOnSource p` (chart-`p` is the unique canonical
chart on its source), the partition-sum `(0,1)`-form
`ω_α := omegaPartitionSum P h_α` has canonical-chart coefficient
`α y` at every `y : X`:
```
ω_α.coeff y ((chartAt ℂ y) y) = α y.
```

This is the operational statement of "α-as-form" recovery: the
partition sum builds a `(0,1)`-form whose chart-`y` view at the
canonical evaluation point `chart_y(y)` is `α y`, exactly matching
the function `α` viewed as the canonical-chart trivialization of its
own `(0,1)`-form. -/
theorem omegaPartitionSum_coeff_at_chart_y_eq_α
    {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (h_chart : ∀ p : X,
      JacobianChallenge.MeromorphicFunctionField.ChartAtConstantOnSource p)
    (y : X) :
    (omegaPartitionSum P h_α).coeff y ((chartAt ℂ y) y) = α y := by
  calc (omegaPartitionSum P h_α).coeff y ((chartAt ℂ y) y)
      = ∑ i : {x : X // x ∈ cover.basePoints},
            localFormCoeff i.val (P.rhoC i * α) y ((chartAt ℂ y) y) := by
        rw [omegaPartitionSum_coeff]
    _ = ∑ i : {x : X // x ∈ cover.basePoints}, (P.rhoC i * α) y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact omegaPartitionSum_per_i_recovery_at_chart_y P α h_chart i y
    _ = α y := sum_rhoC_mul_α_eq_α P α y

end OmegaForm

end JacobianChallenge

end
