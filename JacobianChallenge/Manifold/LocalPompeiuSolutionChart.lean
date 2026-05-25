/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartPullbackExtendZeroSmooth
import JacobianChallenge.Analysis.PompeiuKernelCauchyPompeiu
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-! # Chip 5.3c — chart-x view local identity for the local Pompeiu solution

Combine the partition-of-unity infrastructure (Sub-chip 5.2) with the
chart-pullback-extended-by-zero smoothness package (Sub-chips 5.3a +
5.3b) and the unconditional Cauchy-Pompeiu identity on ℂ (Chip 3c-F-4)
to ship the headline local-solution identity:

```
∀ y ∈ (chartAt ℂ i.val).source,
  partialZBar (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)))
              ((chartAt ℂ i.val) y)
    = (P.rhoC i * α) y.
```

The local solution `u_i^chart : ℂ → ℂ` is the Cauchy-Pompeiu inverse
of the chart-pullback-extended-by-zero of `P.rhoC i * α`. The
hypotheses for Chip 3c-F-4 (`HasCompactSupport` and `ContDiff ℝ 1`
on the input, both via `ContDiff ℝ ∞`) flow from Sub-chips 5.3a + 5.3b
applied to the function `P.rhoC i * α` (manifold-smooth product of
the partition function and α; tsupport contained in
`tsupport (P.rhoC i) ⊆ (chartAt ℂ i.val).source`).

The chart-x view identity reduces, at `ζ := (chartAt ℂ i.val) y` with
`y ∈ chart_xi.source`, the right-hand side of Chip 3c-F-4 to
`(P.rhoC i * α) y` via `chartPullbackZero_eq_α_chartSymm_on_target`
(Sub-chip 5.3a) plus `chart.left_inv`.

This is the final piece of the Sub-chip 5.3 trilogy. Sub-chip 5.4
then multiplies `u_i^chart` (lifted to X) by an extra cutoff `χ_i`
to produce the globally-supported `v_i : X → ℂ` that the
Behnke-Stein-style sum-and-correct argument of Sub-chips 5.5-5.6
assembles.

## Main results

* `tsupport_partition_mul_subset_chart_source` — the tsupport of
  `P.rhoC i * α` lies in `(chartAt ℂ i.val).source` (via
  `tsupport_mul_subset_left` + Sub-chip 5.2's
  `tsupport_rhoC_subset`).
* `contMDiff_partition_mul` — manifold-side smoothness of
  `P.rhoC i * α` (via `ContMDiff.mul`).
* `partialZBar_pompeiuKernel_chartPullbackZero_partition_mul_eq` —
  the headline chart-x view local identity.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function
open JacobianChallenge.PompeiuKernel

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] {cover : FiniteChartCover X}

/-! ## Hypothesis-gathering lemmas for `P.rhoC i * α` -/

/-- The tsupport of `P.rhoC i * α` is contained in the chart source at
the base point `i.val`. Inherited from `tsupport_mul_subset_left` plus
Sub-chip 5.2's `tsupport_rhoC_subset`. -/
theorem tsupport_partition_mul_subset_chart_source
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ) :
    tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source := by
  refine subset_trans ?_ (P.tsupport_rhoC_subset i)
  exact tsupport_mul_subset_left

/-- Register `ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ` locally: ℂ as a real
manifold is a smooth ring. Mirrors the proof of
`instFieldContMDiffRing` in
`Mathlib.Geometry.Manifold.Algebra.Structures` (which only handles
`𝓘(𝕜) n 𝕜`, not the case where the field is a normed algebra over a
smaller base field). Reduces both `contMDiff_add` and `contMDiff_mul`
to their normed-space `ContDiff` counterparts via the `contMDiff_iff`
chart-based characterization. -/
instance contMDiffRing_complex_over_real : ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ where
  contMDiff_add := by
    rw [contMDiff_iff]
    refine ⟨continuous_add, fun x y => ?_⟩
    simp only [mfld_simps, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      Function.comp_id, id_comp, preimage_univ]
    exact contDiff_add.contDiffOn
  contMDiff_mul := by
    rw [contMDiff_iff]
    refine ⟨continuous_mul, fun x y => ?_⟩
    simp only [mfld_simps, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      Function.comp_id, id_comp, preimage_univ]
    exact contDiff_mul.contDiffOn

/-- Manifold-side smoothness of `P.rhoC i * α`: the product of two
manifold-smooth ℂ-valued functions on `X`. Uses the
`ContMDiffRing.toContMDiffMul` instance just registered. -/
theorem contMDiff_partition_mul
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
  (P.rhoC_smooth i).mul h_α

/-! ## The chart-x view local identity -/

/-- **Chip 5.3c headline.** The Pompeiu kernel applied to the
chart-pullback-extended-by-zero of `P.rhoC i * α`, evaluated under
`∂̄` at the chart image of any `y ∈ (chartAt ℂ i.val).source`,
recovers `(P.rhoC i * α) y` — the chart-x view local identity that
Sub-chip 5.4 will combine with cutoffs to assemble the global
`∂̄`-inverse on `X`.

Proof chain:
1. `tsupport (P.rhoC i * α) ⊆ chart_xi.source` (Sub-chip 5.2 + `mul`).
2. `chartPullbackZero i.val (P.rhoC i * α)` is `ContDiff ℝ ∞` and
   `HasCompactSupport` (Sub-chips 5.3a + 5.3b).
3. Chip 3c-F-4 (`partialZBar_pompeiuKernel_eq_self`) gives
   `partialZBar (pompeiuKernel ...) ζ = chartPullbackZero ... ζ`
   for all `ζ : ℂ`, including `ζ := (chart_xi) y`.
4. Inside `chart_xi.target`, the extension equals the bare
   composition; the inner `chart.symm (chart y) = y` collapses
   via `chart_xi.left_inv hy`. -/
theorem partialZBar_pompeiuKernel_chartPullbackZero_partition_mul_eq
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    partialZBar
        (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)))
        ((chartAt ℂ i.val) y)
      = (P.rhoC i * α) y := by
  -- Step 1: tsupport bound.
  have h_tsupport : tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source :=
    tsupport_partition_mul_subset_chart_source P i α
  -- Step 2: manifold-side smoothness of the product.
  have h_prod_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
    contMDiff_partition_mul P i α h_α
  -- Step 3a: ContDiff ℝ ∞ of the chart-pullback-extended-by-zero.
  have h_cpz_smooth :
      ContDiff ℝ ∞ (chartPullbackZero i.val (P.rhoC i * α)) :=
    contDiff_chartPullbackZero i.val (P.rhoC i * α) h_prod_smooth h_tsupport
  -- Step 3b: bring it down to `ContDiff ℝ 1` for Chip 3c-F-4.
  have h_cpz_C1 :
      ContDiff ℝ 1 (chartPullbackZero i.val (P.rhoC i * α)) :=
    h_cpz_smooth.of_le (by exact_mod_cast le_top)
  -- Step 4: HasCompactSupport from Sub-chip 5.3a.
  have h_cpz_cs :
      HasCompactSupport (chartPullbackZero i.val (P.rhoC i * α)) :=
    hasCompactSupport_chartPullbackZero i.val h_tsupport
  -- Step 5: apply Chip 3c-F-4 (unconditional Cauchy-Pompeiu on ℂ).
  have h_cauchy_pompeiu :=
    JacobianChallenge.PompeiuKernel.partialZBar_pompeiuKernel_eq_self
      h_cpz_C1 h_cpz_cs ((chartAt ℂ i.val) y)
  -- `h_cauchy_pompeiu` is now:
  --   partialZBar (pompeiuKernel ...) ((chart_xi) y)
  --     = chartPullbackZero i.val (P.rhoC i * α) ((chart_xi) y)
  rw [h_cauchy_pompeiu]
  -- Step 6: (chart_xi) y ∈ chart_xi.target.
  have h_target : (chartAt ℂ i.val) y ∈ (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).map_source hy
  -- Step 7: chartPullbackZero on target = α ∘ chart.symm.
  rw [chartPullbackZero_eq_α_chartSymm_on_target i.val (P.rhoC i * α) h_target]
  -- Goal: (P.rhoC i * α) (chart.symm (chart y)) = (P.rhoC i * α) y
  -- Use chart.left_inv to collapse chart.symm (chart y) = y.
  show (P.rhoC i * α) ((chartAt ℂ i.val).symm ((chartAt ℂ i.val) y))
        = (P.rhoC i * α) y
  rw [(chartAt ℂ i.val).left_inv hy]

end JacobianChallenge

end
