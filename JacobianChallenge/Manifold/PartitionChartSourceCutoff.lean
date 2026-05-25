/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartitionOfUnitySubordinateToCover
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular

/-! # Chip 5.4a — chart-source cutoff `χ_i`

Construct, for each base point `i` of a `FiniteChartCover`, a smooth
ℝ-valued cutoff `χ_i : X → ℝ` with

* `χ_i ≡ 1` on `tsupport (P.rhoC i)` (a closed subset of
  `(chartAt ℂ i.val).source` by Sub-chip 5.2),
* `χ_i ≡ 0` outside an open set `V` whose closure is contained in
  `(chartAt ℂ i.val).source`,
* `0 ≤ χ_i ≤ 1` pointwise,
* `tsupport χ_i ⊆ (chartAt ℂ i.val).source` (compactly supported in
  the chart source).

The cutoff is the "second cutoff" in the partition-of-unity argument
of Forster Ch. 14: while `P.rhoC i` already satisfies
`tsupport (P.rhoC i) ⊆ chart_xi.source`, multiplying by `α` and
applying `pompeiuKernel` produces a globally smooth ℂ → ℂ function
whose pullback to `X` (composed with `chart_xi`) is well-defined only
on `chart_xi.source`. The cutoff `χ_i` is what makes the resulting
chart-pullback extend by zero to a smooth global X → ℂ function:
`v_i := (χ_i : ℂ) · pompeiuKernel … ∘ chart_xi` (via `Set.indicator`
of `chart_xi.source`) is smooth on all of X precisely because
`tsupport χ_i ⊆ chart_xi.source` — outside `tsupport χ_i` (an open
neighborhood of `chart_xi.sourceᶜ`), the product is identically zero.

The construction:

1. Apply `normal_exists_closure_subset` to the closed set
   `tsupport (P.rhoC i)` and the open set `chart_xi.source` (using
   `NormalSpace X` from `[CompactSpace X] [T2Space X]`) to get an
   open `V` with `tsupport (P.rhoC i) ⊆ V ⊆ closure V ⊆ chart_xi.source`.
2. Apply `exists_contMDiffMap_zero_one_of_isClosed` to the two
   disjoint closed sets `X \ V` and `tsupport (P.rhoC i)` to get
   the smooth bump.
3. Verify `tsupport χ_i ⊆ closure V ⊆ chart_xi.source` via
   `support χ_i ⊆ V` (from `χ_i ≡ 0` on `X \ V`) and closure
   monotonicity.

## Main definitions / results

* `JacobianChallenge.PartitionChartSourceCutoff` — bundled cutoff
  data (the function and its four properties).
* `JacobianChallenge.exists_partitionChartSourceCutoff` — existence,
  via the construction above.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-- A *chart-source cutoff* for base point `i`: a smooth ℝ-valued
function `χ : X → ℝ` that is `1` on `tsupport (P.rhoC i)`,
takes values in `[0, 1]`, and has `tsupport χ ⊆ (chartAt ℂ i.val).source`.

This is the "second cutoff" needed in Forster's globalization
argument: while `P.rhoC i` already vanishes outside `chart.source`,
the additional cutoff `χ` lets us multiply `pompeiuKernel … ∘ chart_xi`
(which is only well-defined on `chart_xi.source`) by `χ` and extend
the product by zero to a globally smooth X → ℂ function. -/
structure PartitionChartSourceCutoff
    {cover : FiniteChartCover X}
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) where
  /-- The cutoff function. -/
  toFun : X → ℝ
  /-- Smoothness. -/
  smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ toFun
  /-- Values in `[0, 1]`. -/
  bounded : ∀ y, toFun y ∈ Set.Icc (0 : ℝ) 1
  /-- Equals `1` on `tsupport (P.rhoC i)`. -/
  eqOne_on_tsupport : Set.EqOn toFun 1 (tsupport (P.rhoC i))
  /-- Topological support contained in the chart source. -/
  tsupport_subset : tsupport toFun ⊆ (chartAt ℂ i.val).source

namespace PartitionChartSourceCutoff

variable {cover : FiniteChartCover X}
  {P : FiniteChartCoverPartition cover}
  {i : {x : X // x ∈ cover.basePoints}}

theorem nonneg (χ : PartitionChartSourceCutoff P i) (y : X) :
    0 ≤ χ.toFun y :=
  (χ.bounded y).1

theorem le_one (χ : PartitionChartSourceCutoff P i) (y : X) :
    χ.toFun y ≤ 1 :=
  (χ.bounded y).2

theorem eqOne_on_support_rhoC (χ : PartitionChartSourceCutoff P i) :
    Set.EqOn χ.toFun 1 (Function.support (P.rhoC i)) :=
  χ.eqOne_on_tsupport.mono (subset_tsupport (P.rhoC i))

end PartitionChartSourceCutoff

/-! ## Existence -/

section Existence

variable {cover : FiniteChartCover X} (P : FiniteChartCoverPartition cover)
  (i : {x : X // x ∈ cover.basePoints})

/-- **Existence of a chart-source cutoff.** Construction:

1. `tsupport (P.rhoC i)` is closed and contained in the open set
   `(chartAt ℂ i.val).source` (Sub-chip 5.2 + `subset_tsupport`).
2. `[CompactSpace X] [T2Space X] ⇒ [NormalSpace X]` (mathlib's
   `NormalSpace.of_compactSpace_r1Space` + T2 ⇒ R1).
3. `normal_exists_closure_subset` produces an open `V` with
   `tsupport (P.rhoC i) ⊆ V ⊆ closure V ⊆ (chartAt ℂ i.val).source`.
4. `exists_contMDiffMap_zero_one_of_isClosed` (between disjoint
   closed sets `X \ V` and `tsupport (P.rhoC i)`) yields the
   smooth cutoff.
5. `support χ ⊆ V` (from `χ ≡ 0` on `X \ V`); closure monotonicity
   gives `tsupport χ ⊆ closure V ⊆ chart_xi.source`. -/
theorem exists_partitionChartSourceCutoff [CompactSpace X] :
    Nonempty (PartitionChartSourceCutoff P i) := by
  classical
  -- Step 1: tsupport ρ_i is closed and lives in chart.source.
  set K : Set X := tsupport (P.rhoC i) with hK_def
  have hK_closed : IsClosed K := isClosed_tsupport _
  have hK_in_source : K ⊆ (chartAt ℂ i.val).source := P.tsupport_rhoC_subset i
  -- Step 2: NormalSpace X is automatic from CompactSpace + T2.
  haveI : NormalSpace X := inferInstance
  -- Step 3: shrink chart.source to a closed-neighborhood of K.
  obtain ⟨V, hV_open, hK_in_V, hV_closure_in_source⟩ :=
    normal_exists_closure_subset hK_closed (chartAt ℂ i.val).open_source hK_in_source
  -- Step 4: smooth bump from `X \ V` to `K`.
  have hVc_closed : IsClosed (Vᶜ) := hV_open.isClosed_compl
  have h_disj : Disjoint (Vᶜ) K := by
    rw [Set.disjoint_iff]
    intro y hy
    exact hy.1 (hK_in_V hy.2)
  obtain ⟨f, hf_zero, hf_one, hf_range⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, ℂ)) hVc_closed hK_closed h_disj
  -- Step 5: extract data.
  refine ⟨{
    toFun := f
    smooth := f.contMDiff
    bounded := hf_range
    eqOne_on_tsupport := hf_one
    tsupport_subset := ?_
  }⟩
  -- tsupport f ⊆ closure V ⊆ chart.source.
  -- support f ⊆ V because f = 0 on Vᶜ.
  have h_support_in_V : Function.support (f : X → ℝ) ⊆ V := by
    intro y hy
    by_contra hy_notin
    -- hy : f y ≠ 0; hy_notin : y ∉ V, i.e., y ∈ Vᶜ.
    have hy_in_Vc : y ∈ Vᶜ := hy_notin
    have h_f_zero : (f : X → ℝ) y = 0 := hf_zero hy_in_Vc
    exact hy h_f_zero
  calc tsupport (f : X → ℝ)
      = closure (Function.support (f : X → ℝ)) := rfl
    _ ⊆ closure V := closure_mono h_support_in_V
    _ ⊆ (chartAt ℂ i.val).source := hV_closure_in_source

end Existence

end JacobianChallenge

end
