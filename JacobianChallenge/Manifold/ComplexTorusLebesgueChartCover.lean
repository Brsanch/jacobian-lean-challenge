/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import JacobianChallenge.Manifold.SmoothPathIntegral
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Archimedean.Basic

set_option linter.unusedSectionVars false

/-! # Lebesgue chart-anchor partition for `SmoothPath` on `ℂ ⧸ L`

For a smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, the image of
`γ.ambient` on `Set.Icc 0 1` is contained in a finite union of chart
sources of the torus atlas. The Lebesgue number lemma + compactness
of `Icc 0 1` gives a uniform `δ > 0` such that any `δ`-ball around
any point of `Icc 0 1` maps under `γ.ambient` into a single chart's
source.

This chip refines that uniform `δ` into an explicit equidistant
partition `{[k/N, (k+1)/N]}_{k=0..N-1}` of `[0, 1]` with `1/N < δ`,
and records the chart-anchor `xs : Fin N → ℂ` per sub-interval so that
`γ.ambient([k/N, (k+1)/N]) ⊆ (localChart L _ (xs k)).symm.source`.

The argument mirrors `S2LoopChartPartition` (used for the polygonal-
approximation arc on `S²`), but the chart cover here is *infinite*
(one chart per anchor `x ∈ ℂ`) rather than the fixed two-chart cover
on `S²`. The Lebesgue lemma still applies because the cover is open
and the parameter space `Icc 0 1 ⊆ ℝ` is compact.

## What this file ships

* `ComplexTorus.smoothPath_chart_anchor_cover` — the uniform `δ` from
  the Lebesgue number lemma applied to the chart-pullback cover, with
  the quantifier restricted to `t ∈ Icc 0 1`.

* `ComplexTorus.exists_chartAnchor_partition` — refines the uniform
  `δ` into an explicit equidistant `Fin N` partition with per-piece
  anchors `xs : Fin N → ℂ`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Metric Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Open cover of `ℝ` by chart-source preimages -/

/-- For each `x : ℂ`, the preimage under `γ.ambient` of the chart-source
`(localChart L _ x).symm.source` is open in `ℝ`. -/
private lemma chartSource_preimage_isOpen
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x : ℂ) :
    IsOpen (γ.ambient ⁻¹' (localChart L (discRadius_separates L) x).symm.source) := by
  have h_amb_cont : Continuous γ.ambient := γ.ambient_contMDiff.continuous
  exact ((localChart L (discRadius_separates L) x).symm.open_source).preimage h_amb_cont

/-- For each `t : ℝ`, the preimage at the anchor `(γ.ambient t).out` contains `t`. -/
private lemma t_mem_chartSource_preimage_at_out
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (t : ℝ) :
    t ∈ γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (γ.ambient t).out).symm.source := by
  show γ.ambient t ∈
      (localChart L (discRadius_separates L) (γ.ambient t).out).symm.source
  exact mem_chart_source ℂ (γ.ambient t)

/-- The chart-pullback cover of `ℝ`: indexing by `ℂ`, each `x : ℂ` gives
the open set `γ.ambient ⁻¹' (localChart L _ x).symm.source`. The union
over all `x ∈ ℂ` covers all of `ℝ`. -/
private lemma chartPreimage_cover
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    (Set.univ : Set ℝ) ⊆
      ⋃ x : ℂ, γ.ambient ⁻¹' (localChart L (discRadius_separates L) x).symm.source := by
  intro t _
  refine mem_iUnion.mpr ⟨(γ.ambient t).out, ?_⟩
  exact t_mem_chartSource_preimage_at_out L γ t

/-! ## Uniform Lebesgue radius for the chart cover on `Icc 0 1` -/

/-- **Lebesgue radius for the chart cover on `Icc 0 1`.** For every smooth
path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, there is `δ > 0` such that for
every `t ∈ Icc 0 1`, there is an anchor `x : ℂ` with the `δ`-ball
around `t` (in `ℝ`) contained in
`γ.ambient ⁻¹' (localChart L _ x).symm.source`. -/
theorem smoothPath_chart_anchor_cover
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ x : ℂ,
      Metric.ball t δ ⊆
        γ.ambient ⁻¹' (localChart L (discRadius_separates L) x).symm.source := by
  let U : ℂ → Set ℝ := fun x =>
    γ.ambient ⁻¹' (localChart L (discRadius_separates L) x).symm.source
  have hU_open : ∀ x : ℂ, IsOpen (U x) := fun x =>
    chartSource_preimage_isOpen L γ x
  have hcover_Icc : (Set.Icc (0 : ℝ) 1) ⊆ ⋃ x, U x :=
    subset_trans (subset_univ _) (chartPreimage_cover L γ)
  obtain ⟨V, hV_uni, hV_ball⟩ :=
    lebesgue_number_lemma (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      hU_open hcover_Icc
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_uniformity_dist.mp hV_uni
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  obtain ⟨x_t, hx_t_sub⟩ := hV_ball t ht
  refine ⟨x_t, ?_⟩
  intro y hy
  have h_dist : dist t y < δ := by
    rw [Metric.mem_ball] at hy; rwa [dist_comm]
  have h_pair : (t, y) ∈ V := hδ_sub h_dist
  exact hx_t_sub h_pair

/-! ## Equidistant `Fin N` partition with chart anchors -/

/-- **Chart-anchor equidistant partition.** For every smooth path
`γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)`, there exist `N : ℕ` with `0 < N`
and chart anchors `xs : Fin N → ℂ` such that for every `k : Fin N`
and every `s ∈ ℝ` with `(k : ℝ) / N ≤ s ≤ ((k : ℝ) + 1) / N`,
`γ.ambient s` lies in the source of the chart at anchor `xs k`. -/
theorem exists_chartAnchor_partition
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    ∃ N : ℕ, 0 < N ∧ ∃ xs : Fin N → ℂ,
      ∀ (k : Fin N) (s : ℝ),
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈
          (localChart L (discRadius_separates L) (xs k)).symm.source := by
  -- Step 1: Lebesgue radius δ > 0.
  obtain ⟨δ, hδ_pos, hball⟩ := smoothPath_chart_anchor_cover L γ
  -- Step 2: pick N ≥ 1 with 1/N < δ.
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  let N : ℕ := max M 1
  have hN_pos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hN_cast_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have h_inv_delta_pos : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδ_pos
  have hM_cast_pos : (0 : ℝ) < M := lt_trans h_inv_delta_pos hM
  have hM_pos : 0 < M := by exact_mod_cast hM_cast_pos
  have h_one_lt_M_delta : (1 : ℝ) < M * δ := (div_lt_iff₀ hδ_pos).mp hM
  have h_inv_M_lt : (1 : ℝ) / M < δ := by
    rw [div_lt_iff₀ hM_cast_pos]; linarith
  have hN_ge_M : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left _ _
  have hN_inv : (1 : ℝ) / N < δ := by
    have h_le : (1 : ℝ) / N ≤ 1 / M :=
      one_div_le_one_div_of_le hM_cast_pos hN_ge_M
    linarith
  -- Step 3: midpoint c_k = (2k+1)/(2N) ∈ Icc 0 1 of [k/N, (k+1)/N].
  have h_ck_in_Icc : ∀ k : Fin N, ((2 * (k : ℝ) + 1) / (2 * N)) ∈
      Set.Icc (0 : ℝ) 1 := by
    intro k
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one (by positivity)]
      have hk : (k : ℕ) + 1 ≤ N := k.isLt
      have hk_real : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
      linarith
  -- Step 4: for each k, get an anchor x_k via the Lebesgue lemma at c_k.
  classical
  let xs : Fin N → ℂ := fun k =>
    Classical.choose (hball _ (h_ck_in_Icc k))
  have hxs_spec : ∀ k : Fin N,
      Metric.ball ((2 * (k : ℝ) + 1) / (2 * N)) δ ⊆
        γ.ambient ⁻¹'
          (localChart L (discRadius_separates L) (xs k)).symm.source := fun k =>
    Classical.choose_spec (hball _ (h_ck_in_Icc k))
  refine ⟨N, hN_pos, xs, ?_⟩
  intro k s hs_lower hs_upper
  -- Show s ∈ ball c_k δ, then apply hxs_spec.
  have h_dist_lhs : s - (2 * (k : ℝ) + 1) / (2 * N) ≤ 1 / (2 * N) := by
    have h_k_eq : ((k : ℝ) + 1) / N = (2 * (k : ℝ) + 2) / (2 * N) := by
      field_simp
    rw [h_k_eq] at hs_upper
    have h_diff : (2 * (k : ℝ) + 2) / (2 * N) - (2 * (k : ℝ) + 1) / (2 * N)
        = 1 / (2 * N) := by ring
    linarith
  have h_dist_rhs : (2 * (k : ℝ) + 1) / (2 * N) - s ≤ 1 / (2 * N) := by
    have h_k_eq : ((k : ℝ)) / N = (2 * (k : ℝ)) / (2 * N) := by field_simp
    rw [h_k_eq] at hs_lower
    have h_diff : (2 * (k : ℝ) + 1) / (2 * N) - (2 * (k : ℝ)) / (2 * N)
        = 1 / (2 * N) := by ring
    linarith
  have h_abs : |s - (2 * (k : ℝ) + 1) / (2 * N)| ≤ 1 / (2 * N) :=
    abs_le.mpr ⟨by linarith, h_dist_lhs⟩
  have h_inv2N_lt : (1 : ℝ) / (2 * N) < δ := by
    have h_half_le : (1 : ℝ) / (2 * N) ≤ 1 / N := by
      apply div_le_div_of_nonneg_left _ hN_cast_pos
      · linarith
      · norm_num
    linarith
  have h_dist_lt : dist s ((2 * (k : ℝ) + 1) / (2 * N)) < δ := by
    rw [Real.dist_eq]
    linarith
  have h_in_ball : s ∈ Metric.ball ((2 * (k : ℝ) + 1) / (2 * N)) δ := by
    rw [Metric.mem_ball]; exact h_dist_lt
  exact hxs_spec k h_in_ball

end ComplexTorus

end JacobianChallenge

end
