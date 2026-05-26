/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalPompeiuSolutionChart
import JacobianChallenge.Manifold.LocalPompeiuSolutionGlobal
import JacobianChallenge.Manifold.PartialZBarManifoldAtChart
import JacobianChallenge.Manifold.GlobalSolutionCandidatePartialZBar

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Sub-chip 5.5c-I-f — chart-anchored Leibniz decomposition of `v_i`

Explicit Leibniz decomposition of the chart-anchored `∂̄` of the
local Pompeiu solution `v_i := (χ_i : ℂ) · K_i ∘ chart_{i.val}`,
where `K_i := pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))`.

For `y ∈ (chartAt ℂ i.val).source`:
```
partialZBarManifoldAtChart i.val v_i y
  = partialZBarManifoldAtChart i.val (χ_i : X → ℂ) y · K_i(chart_{i.val} y)
  + χ_i(y) · (P.rhoC i * α)(y).
```

The first term is the **cutoff-derivative term** (the genuine outer-
ring leakage); the second is the **Pompeiu identity term** (using
Sub-chip 5.3c). On `support (P.rhoC i)`, `χ_i ≡ 1` (Sub-chip 5.4a), so
the first term vanishes and the formula collapses to the
`(P.rhoC i * α)(y)` identity from Sub-chip 5.5b. On the outer ring
`tsupport χ_i \ support (P.rhoC i)`, `(P.rhoC i * α)(y) = 0` and the
formula collapses to the cutoff-derivative-times-`K_i`.

This isolates the outer-ring leakage as a precise computable
expression for any future cancellation / iteration argument
(`Sub-chip 5.5c-I-g` and beyond).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Function
open JacobianChallenge.PompeiuKernel

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
  {cover : FiniteChartCover X}

/-! ## Identification of `v_i ∘ chart_{i.val}.symm` on `chart_{i.val}.target` -/

/-- On `(chartAt ℂ i.val).target`, the chart-pullback of `v_i` factors
as `(χ_i : ℂ) ∘ chart_{i.val}.symm` times `pompeiuKernel
(chartPullbackZero i.val (P.rhoC i * α))`. The simplification uses
`chart_{i.val}.right_inv` to collapse `chart_{i.val} ∘ chart_{i.val}.symm`
to the identity on the target. -/
lemma localPompeiuSolutionGlobal_chart_symm_eqOn_target
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) (α : X → ℂ)
    (χ : PartitionChartSourceCutoff P i) :
    EqOn
      ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ i.val).symm)
      (fun z : ℂ =>
        ((χ.toFun ((chartAt ℂ i.val).symm z) : ℝ) : ℂ) *
        pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) z)
      (chartAt ℂ i.val).target := by
  intro z hz
  show (localPompeiuSolutionGlobal P i α χ) ((chartAt ℂ i.val).symm z)
      = ((χ.toFun ((chartAt ℂ i.val).symm z) : ℝ) : ℂ) *
        pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) z
  unfold localPompeiuSolutionGlobal
  rw [(chartAt ℂ i.val).right_inv hz]

/-! ## Differentiability at `chart_{i.val}(y)` -/

/-- `(χ.toFun : X → ℂ) ∘ chart_{i.val}.symm` is `DifferentiableAt ℝ`
at `(chartAt ℂ i.val) y` for `y ∈ chart_{i.val}.source`. From χ's
manifold-smoothness via `differentiableAt_extChartAt_pullback_of_contMDiff`. -/
lemma differentiableAt_chiC_chart_symm
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    DifferentiableAt ℝ
      ((fun z : X => ((χ.toFun z : ℝ) : ℂ)) ∘ (chartAt ℂ i.val).symm)
      ((chartAt ℂ i.val) y) := by
  have h_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun z : X => ((χ.toFun z : ℝ) : ℂ)) := by
    have h_χ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ χ.toFun := χ.smooth
    have h_cast : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
        (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contMDiff
    exact h_cast.comp h_χ
  exact differentiableAt_extChartAt_pullback_of_contMDiff
    (u := fun z : X => ((χ.toFun z : ℝ) : ℂ)) h_smooth i.val y hy

/-- `pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))` is
`DifferentiableAt ℝ` at any `ζ : ℂ`. Follows from Chip 2d's
`contDiff_pompeiuKernel_infty` plus the smoothness +
compact-support of `chartPullbackZero i.val (P.rhoC i * α)`
(Sub-chips 5.3a/b). -/
lemma differentiableAt_pompeiuKernel_chartPullbackZero
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints}) {α : X → ℂ}
    (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) (ζ : ℂ) :
    DifferentiableAt ℝ
      (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) ζ := by
  have h_prod : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (P.rhoC i * α) :=
    contMDiff_partition_mul P i α h_α
  have h_supp : tsupport (P.rhoC i * α) ⊆ (chartAt ℂ i.val).source :=
    tsupport_partition_mul_subset_chart_source P i α
  have h_cpz_smooth :
      ContDiff ℝ ∞ (chartPullbackZero i.val (P.rhoC i * α)) :=
    contDiff_chartPullbackZero i.val (P.rhoC i * α) h_prod h_supp
  have h_cpz_compact :
      HasCompactSupport (chartPullbackZero i.val (P.rhoC i * α)) :=
    hasCompactSupport_chartPullbackZero i.val h_supp
  have h_pK_smooth :
      ContDiff ℝ ∞ (pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))) :=
    contDiff_pompeiuKernel_infty h_cpz_smooth h_cpz_compact
  exact h_pK_smooth.differentiable (by decide) |>.differentiableAt

/-! ## Chart-anchored Leibniz decomposition -/

/-- **Chart-anchored Leibniz decomposition of `v_i`.** For
`y ∈ (chartAt ℂ i.val).source`:
```
partialZBarManifoldAtChart i.val v_i y
  = partialZBarManifoldAtChart i.val (χ_i : X → ℂ) y · K_i(chart_{i.val} y)
  + χ_i(y) · (P.rhoC i * α)(y).
```

The first term is the **cutoff-derivative outer-ring leakage**; the
second is the **Pompeiu identity term** that recovers `(P.rhoC i * α)`
on `support (P.rhoC i)` (where `χ_i ≡ 1` ⟹ `∂̄χ_i = 0` ⟹ first term
vanishes ⟹ identity collapses to Sub-chip 5.5b's). -/
theorem partialZBarManifoldAtChart_localPompeiuSolutionGlobal_leibniz
    (P : FiniteChartCoverPartition cover)
    (i : {x : X // x ∈ cover.basePoints})
    {α : X → ℂ} (h_α : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (χ : PartitionChartSourceCutoff P i)
    {y : X} (hy : y ∈ (chartAt ℂ i.val).source) :
    partialZBarManifoldAtChart i.val (localPompeiuSolutionGlobal P i α χ) y
      = partialZBarManifoldAtChart i.val
          (fun z : X => ((χ.toFun z : ℝ) : ℂ)) y *
          pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
            ((chartAt ℂ i.val) y)
        + ((χ.toFun y : ℝ) : ℂ) * (P.rhoC i * α) y := by
  -- Unfold partialZBarManifoldAtChart to partialZBar of chart pullback.
  show partialZBar
      ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ i.val).symm)
      ((chartAt ℂ i.val) y)
    = partialZBar
        ((fun z : X => ((χ.toFun z : ℝ) : ℂ)) ∘ (chartAt ℂ i.val).symm)
        ((chartAt ℂ i.val) y) *
        pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α))
          ((chartAt ℂ i.val) y)
      + ((χ.toFun y : ℝ) : ℂ) * (P.rhoC i * α) y
  -- Replace LHS's chart pullback by the explicit product via germ-eq + EventuallyEq.fderiv_eq.
  have h_target_open : IsOpen (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).open_target
  have hy_tgt : (chartAt ℂ i.val) y ∈ (chartAt ℂ i.val).target :=
    (chartAt ℂ i.val).map_source hy
  have h_evEq :
      ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ i.val).symm)
        =ᶠ[𝓝 ((chartAt ℂ i.val) y)]
      (fun z : ℂ =>
        ((χ.toFun ((chartAt ℂ i.val).symm z) : ℝ) : ℂ) *
        pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) z) := by
    filter_upwards [h_target_open.mem_nhds hy_tgt] with z hz
    exact localPompeiuSolutionGlobal_chart_symm_eqOn_target P i α χ hz
  -- Introduce f := χ ∘ chart_{i.val}.symm and g := pompeiuKernel(...) as ℂ → ℂ.
  set f : ℂ → ℂ :=
    fun z : ℂ => ((χ.toFun ((chartAt ℂ i.val).symm z) : ℝ) : ℂ) with hf_def
  set g : ℂ → ℂ :=
    pompeiuKernel (chartPullbackZero i.val (P.rhoC i * α)) with hg_def
  -- Rewrite the chart pullback of v_i as f * g via EventuallyEq.fderiv_eq.
  have h_evEq' : ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ i.val).symm)
      =ᶠ[𝓝 ((chartAt ℂ i.val) y)] (f * g) := by
    filter_upwards [h_target_open.mem_nhds hy_tgt] with z hz
    show (localPompeiuSolutionGlobal P i α χ) ((chartAt ℂ i.val).symm z)
        = f z * g z
    rw [hf_def, hg_def]
    exact localPompeiuSolutionGlobal_chart_symm_eqOn_target P i α χ hz
  have h_lhs_eq :
      partialZBar ((localPompeiuSolutionGlobal P i α χ) ∘ (chartAt ℂ i.val).symm)
          ((chartAt ℂ i.val) y)
        = partialZBar (f * g) ((chartAt ℂ i.val) y) := by
    unfold partialZBar
    rw [Filter.EventuallyEq.fderiv_eq h_evEq']
  rw [h_lhs_eq]
  -- Apply Leibniz on partialZBar (f * g).
  have h_f_diff : DifferentiableAt ℝ f ((chartAt ℂ i.val) y) :=
    differentiableAt_chiC_chart_symm P i χ hy
  have h_g_diff : DifferentiableAt ℝ g ((chartAt ℂ i.val) y) :=
    differentiableAt_pompeiuKernel_chartPullbackZero P i h_α ((chartAt ℂ i.val) y)
  rw [partialZBar_mul h_f_diff h_g_diff]
  -- Identify f at chart_{i.val} y with (χ.toFun y : ℂ).
  have h_chart_left_inv : (chartAt ℂ i.val).symm ((chartAt ℂ i.val) y) = y :=
    (chartAt ℂ i.val).left_inv hy
  have h_f_apply : f ((chartAt ℂ i.val) y) = ((χ.toFun y : ℝ) : ℂ) := by
    show ((χ.toFun ((chartAt ℂ i.val).symm ((chartAt ℂ i.val) y)) : ℝ) : ℂ)
        = ((χ.toFun y : ℝ) : ℂ)
    rw [h_chart_left_inv]
  -- Identify partialZBar g at chart_{i.val} y with (P.rhoC i * α)(y) via 5.3c.
  have h_pK_id : partialZBar g ((chartAt ℂ i.val) y) = (P.rhoC i * α) y :=
    partialZBar_pompeiuKernel_chartPullbackZero_partition_mul_eq P i α h_α hy
  -- The remaining `partialZBar f ...` on the goal matches the RHS's first factor since
  -- partialZBar uses fderiv, and `f` ∘ chart-symm is the same function up to defeq.
  rw [h_pK_id, h_f_apply]
  -- Match partialZBar f with the RHS's first factor; both equal
  -- partialZBar((fun z : X => ((χ.toFun z : ℝ) : ℂ)) ∘ (chartAt ℂ i.val).symm) (...).
  rfl

end JacobianChallenge

end
