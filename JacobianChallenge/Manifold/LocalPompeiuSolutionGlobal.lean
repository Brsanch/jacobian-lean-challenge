/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionChart
import JacobianChallenge.Manifold.PartitionChartSourceCutoff
import JacobianChallenge.Analysis.PompeiuKernelSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Chip 5.4b — global Pompeiu solution `v_i : X → ℂ`

Combine the chart-x view local identity (Sub-chip 5.3c) with the
chart-source cutoff (Sub-chip 5.4a) to produce a globally smooth
`v_i : X → ℂ` with `tsupport v_i ⊆ (chartAt ℂ i.val).source`.

The construction:

```
v_i y := (χ.toFun y : ℂ) ·
          pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                        ((chartAt ℂ i.val) y)
```

This is a *total* function `X → ℂ`. The chart `chartAt ℂ i.val : X → ℂ`
is total (it's a `PartialHomeomorph` whose underlying `toFun` is
total) — only continuous on `chart_xi.source`. The Pompeiu kernel
factor is therefore well-defined everywhere on `X`, possibly with
junk values outside `chart_xi.source`. Multiplying by `(χ : ℂ)`
(which vanishes outside `tsupport χ ⊆ chart_xi.source` by
Sub-chip 5.4a) gracefully zeros out those junk values.

Global smoothness comes from the open cover
`{chart_xi.source, (tsupport χ)ᶜ}` of `X`:

* On `chart_xi.source` (open), the chart `chart_xi` is smooth
  (`contMDiffOn_chart`), `pompeiuKernel …` is globally `ContDiff ℝ ∞`
  (Chip 2d), and `χ` is smooth (5.4a), so the product is smooth.
* On `(tsupport χ)ᶜ` (open), `χ ≡ 0`, hence `v_i ≡ 0`, smooth.

The two sets cover `X` because `tsupport χ ⊆ chart_xi.source`
(5.4a's `tsupport_subset`), so `chart_xi.sourceᶜ ⊆ (tsupport χ)ᶜ`.

## Main results

* `localPompeiuSolutionGlobal P i α χ : X → ℂ` — the global solution.
* `tsupport_localPompeiuSolutionGlobal_subset` — the tsupport bound.
* `contMDiff_localPompeiuSolutionGlobal` — global smoothness.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold Topology ContDiff
open Set Function
open JacobianChallenge.PompeiuKernel

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X] {cover : FiniteChartCover X}

/-- The **global Pompeiu solution** at base point `i`, obtained by
multiplying the chart-pullback Pompeiu kernel by the chart-source
cutoff `χ`. Total function `X → ℂ`. -/
def localPompeiuSolutionGlobal
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i) : X → ℂ :=
  fun y =>
    ((χ.toFun y : ℝ) : ℂ) *
      pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                    ((chartAt ℂ i.val) y)

/-! ## tsupport bound -/

/-- The (function-theoretic) support of `v_i` is contained in the
support of `χ`: any `y` with `v_i y ≠ 0` must have `χ y ≠ 0`. -/
theorem support_localPompeiuSolutionGlobal_subset
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i) :
    Function.support (localPompeiuSolutionGlobal P i α χ)
      ⊆ Function.support χ.toFun := by
  intro y hy
  -- hy : v_i y ≠ 0; want : χ y ≠ 0.
  by_contra h_chi_zero
  apply hy
  unfold localPompeiuSolutionGlobal
  simp only [Function.notMem_support] at h_chi_zero
  rw [h_chi_zero]
  simp

/-- The topological support of `v_i` is contained in
`(chartAt ℂ i.val).source` — from the chain
`tsupport v_i ⊆ tsupport χ ⊆ chart_xi.source` (Sub-chip 5.4a). -/
theorem tsupport_localPompeiuSolutionGlobal_subset
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i) :
    tsupport (localPompeiuSolutionGlobal P i α χ)
      ⊆ (chartAt ℂ i.val).source := by
  calc tsupport (localPompeiuSolutionGlobal P i α χ)
      = closure (Function.support (localPompeiuSolutionGlobal P i α χ)) := rfl
    _ ⊆ closure (Function.support χ.toFun) :=
        closure_mono (support_localPompeiuSolutionGlobal_subset P i α χ)
    _ = tsupport χ.toFun := rfl
    _ ⊆ (chartAt ℂ i.val).source := χ.tsupport_subset

/-! ## Global smoothness -/

/-- The composition `pompeiuKernel (chartPullbackZero …) ∘ (chartAt ℂ i.val)`
is `ContMDiffOn` on the chart source: on this open set the chart is
manifold-smooth (`contMDiffOn_chart`), and `pompeiuKernel … : ℂ → ℂ`
is globally `ContDiff ℝ ∞` (Chip 2d) hence `ContMDiff` between the
trivial models. -/
theorem contMDiffOn_pompeiuKernel_comp_chart
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun y : X => pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                                  ((chartAt ℂ i.val) y))
      (chartAt ℂ i.val).source := by
  -- Step 1: pompeiuKernel (chartPullbackZero …) is ContDiff ℝ ∞.
  have h_tsupport :
      tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source :=
    tsupport_partition_mul_subset_chart_source P i α
  have h_prod_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
    contMDiff_partition_mul P i α h_α
  have h_cpz_smooth :
      ContDiff ℝ ∞ (chartPullbackZero i.val (P.rhoC i * α)) :=
    contDiff_chartPullbackZero i.val (P.rhoC i * α) h_prod_smooth h_tsupport
  have h_cpz_cs :
      HasCompactSupport (chartPullbackZero i.val (P.rhoC i * α)) :=
    hasCompactSupport_chartPullbackZero i.val h_tsupport
  have h_pk_smooth :
      ContDiff ℝ ∞ (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) :=
    contDiff_pompeiuKernel_infty h_cpz_smooth h_cpz_cs
  -- Step 2: convert to manifold smoothness.
  have h_pk_mdiff :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) :=
    h_pk_smooth.contMDiff
  -- Step 3: chart_xi is ContMDiffOn on its source (at level ⊤, lowered to ∞).
  have h_chart_mdiffOn_top :
      ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤
        (chartAt ℂ i.val) (chartAt ℂ i.val).source :=
    contMDiffOn_chart (I := (𝓘(ℝ, ℂ))) (n := ⊤) (x := i.val)
  have h_chart_mdiffOn :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (chartAt ℂ i.val) (chartAt ℂ i.val).source :=
    h_chart_mdiffOn_top.of_le (by exact_mod_cast le_top)
  -- Step 4: compose.
  exact h_pk_mdiff.comp_contMDiffOn h_chart_mdiffOn

/-- **Global smoothness of `v_i`.** On the open cover
`{chart_xi.source, (tsupport χ)ᶜ}` (which exhausts `X` via
Sub-chip 5.4a's `tsupport_subset`), the function is smooth on each
piece: on `chart_xi.source` as a product of smooth factors; on
`(tsupport χ)ᶜ` as identically zero (since `χ ≡ 0` outside its
support, and `support ⊆ tsupport`). -/
theorem contMDiff_localPompeiuSolutionGlobal
    [CompactSpace X] (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (α : X → ℂ)
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (localPompeiuSolutionGlobal P i α χ) := by
  -- ContMDiff is pointwise ContMDiffAt; case-split on y ∈ chart.source vs not.
  intro y
  -- Setup: pompeiuKernel composed with chart is ContMDiffOn chart.source.
  have h_PKcc_mdiffOn :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (fun y : X => pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                                    ((chartAt ℂ i.val) y))
        (chartAt ℂ i.val).source :=
    contMDiffOn_pompeiuKernel_comp_chart P i α h_α
  -- χ as ℂ-valued, manifold-smooth globally.
  have h_chi_R_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ.toFun := χ.smooth
  have h_ofRealCLM :
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (Complex.ofRealCLM : ℝ → ℂ) :=
    Complex.ofRealCLM.contMDiff
  have h_chi_C_smooth :
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (fun y : X => ((χ.toFun y : ℝ) : ℂ)) :=
    h_ofRealCLM.comp h_chi_R_smooth
  by_cases hy : y ∈ (chartAt ℂ i.val).source
  · -- Case 1: y ∈ chart.source. Both factors smooth at y.
    have h_chart_source_open : IsOpen (chartAt ℂ i.val).source :=
      (chartAt ℂ i.val).open_source
    have h_PKcc_mdiffAt :
        ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
          (fun y : X => pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
                                      ((chartAt ℂ i.val) y))
          y :=
      h_PKcc_mdiffOn.contMDiffAt (h_chart_source_open.mem_nhds hy)
    have h_chi_C_mdiffAt :
        ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
          (fun y : X => ((χ.toFun y : ℝ) : ℂ)) y :=
      h_chi_C_smooth.contMDiffAt
    -- Product of two ContMDiffAt — uses contMDiffRing_complex_over_real.
    exact h_chi_C_mdiffAt.mul h_PKcc_mdiffAt
  · -- Case 2: y ∉ chart.source ⇒ y ∉ tsupport χ.
    have hy_not_tsupp : y ∉ tsupport χ.toFun := by
      intro h_in_tsupp
      exact hy (χ.tsupport_subset h_in_tsupp)
    -- On the open neighborhood (tsupport χ)ᶜ of y, v_i ≡ 0.
    have h_tsupport_closed : IsClosed (tsupport χ.toFun) :=
      isClosed_tsupport _
    have h_compl_open : IsOpen (tsupport χ.toFun)ᶜ :=
      h_tsupport_closed.isOpen_compl
    have h_nhd : (tsupport χ.toFun)ᶜ ∈ 𝓝 y :=
      h_compl_open.mem_nhds hy_not_tsupp
    -- v_i =ᶠ[𝓝 y] fun _ => 0 via filter_upwards on the open neighborhood.
    have h_evEq :
        (localPompeiuSolutionGlobal P i α χ) =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
      filter_upwards [h_nhd] with z hz_compl
      have h_chi_z_zero : χ.toFun z = 0 := by
        have h_z_not_supp : z ∉ Function.support χ.toFun :=
          fun h => hz_compl (subset_tsupport _ h)
        exact Function.notMem_support.mp h_z_not_supp
      unfold localPompeiuSolutionGlobal
      simp [h_chi_z_zero]
    -- Apply congr_of_eventuallyEq: from `g = const 0` smooth and `v_i =ᶠ g`,
    -- conclude v_i is smooth at y.
    have h_const : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun _ : X => (0 : ℂ)) y :=
      contMDiffAt_const
    exact h_const.congr_of_eventuallyEq h_evEq

end JacobianChallenge

end
