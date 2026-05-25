/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.ComplexManifoldRealification
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Algebra.Order.Archimedean.Basic

set_option linter.unusedSectionVars false

/-! # Equidistant chart-image-ball partition for a `SmoothPath` on a complex 1-manifold

Path-level analog of `UniformChartContainmentDepth_named` (which provides
the corresponding partition for the 2-simplex parameter space). For every
smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) X` on an arbitrary complex 1-manifold
`X` modelled on `ℂ` with holomorphic structure
`[IsManifold (𝓘(ℂ, ℂ)) ω X]`, there is an equidistant partition of `[0, 1]`
into `N` segments and a chart anchor `qs k : X` per segment such that on
each `[k/N, (k+1)/N]`:

  * `γ.ambient s ∈ (chartAt ℂ (qs k)).source`, and
  * `(chartAt ℂ (qs k)) (γ.ambient s) ∈ Metric.ball
      ((chartAt ℂ (qs k)) (qs k)) (chartBallRadius (qs k))`,

where `chartBallRadius (qs k) > 0` and the ball lies inside the chart
target.

This is the path-level building block paired with the ball-data machinery
from `AffineChartTriangleSimplexBall`, `ChartStraightLinePathBall`, and
`FanTriangulationBall`: every smooth segment of `γ` lives inside a single
chart-image ball, so a chart-local polygonal approximation is available.

The argument is the standard Lebesgue-number-lemma application to the
open cover of `Icc (0:ℝ) 1` by chart-ball pullbacks `γ.ambient ⁻¹'
chartBallSourcePreimage q` (one per `q : X`). Refining the resulting
uniform `δ > 0` into an equidistant `Fin N` partition follows the same
pattern as `ComplexTorus.exists_chartAnchor_partition` but with the
arbitrary-X chart `chartAt ℂ q` in place of the torus-specific
`localChart L _ x`.

## What this file ships

* `chartBallRadius q` — a positive radius such that
  `Metric.ball ((chartAt ℂ q) q) (chartBallRadius q) ⊆ (chartAt ℂ q).target`.
* `chartBallSourcePreimage q` — open subset of `(chartAt ℂ q).source`
  whose chart-image lies in the chart ball at `q`.
* `smoothPath_chart_ball_anchor_cover` — Lebesgue radius for the
  chart-ball-pullback cover restricted to `Icc 0 1`.
* `exists_chartBall_anchor_partition` — equidistant `Fin N` partition
  with per-segment anchors `qs : Fin N → X` such that each segment
  maps under `γ.ambient` into the corresponding `chartBallSourcePreimage`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Metric Filter Topology
open scoped Manifold ContDiff

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Chart-ball radius and chart-ball source preimage -/

/-- For each `q : X`, an `r > 0` with
`Metric.ball ((chartAt ℂ q) q) r ⊆ (chartAt ℂ q).target`. Exists
because `(chartAt ℂ q).target` is open and contains `(chartAt ℂ q) q`. -/
private lemma exists_chartBallRadius (q : X) :
    ∃ r > 0, Metric.ball ((chartAt ℂ q) q) r ⊆ (chartAt ℂ q).target :=
  Metric.isOpen_iff.mp (chartAt ℂ q).open_target _ (mem_chart_target ℂ q)

/-- A specific positive radius witnessing the chart-ball containment at `q`. -/
noncomputable def chartBallRadius (q : X) : ℝ :=
  Classical.choose (exists_chartBallRadius q)

lemma chartBallRadius_pos (q : X) : 0 < chartBallRadius q :=
  (Classical.choose_spec (exists_chartBallRadius q)).1

lemma chartBallRadius_subset_target (q : X) :
    Metric.ball ((chartAt ℂ q) q) (chartBallRadius q) ⊆ (chartAt ℂ q).target :=
  (Classical.choose_spec (exists_chartBallRadius q)).2

/-- Points of `X` whose chart-image under `chartAt ℂ q` lies in the chosen
chart-ball at `q`. Open subset of `(chartAt ℂ q).source`. -/
noncomputable def chartBallSourcePreimage (q : X) : Set X :=
  (chartAt ℂ q).source ∩
    (chartAt ℂ q) ⁻¹' Metric.ball ((chartAt ℂ q) q) (chartBallRadius q)

lemma chartBallSourcePreimage_isOpen (q : X) :
    IsOpen (chartBallSourcePreimage q) :=
  (chartAt ℂ q).isOpen_inter_preimage Metric.isOpen_ball

lemma chartBallSourcePreimage_mem_self (q : X) :
    q ∈ chartBallSourcePreimage q := by
  refine ⟨mem_chart_source ℂ q, ?_⟩
  rw [Set.mem_preimage]
  exact Metric.mem_ball_self (chartBallRadius_pos q)

/-! ## Pullback cover of `(Set.univ : Set ℝ)` -/

variable (γ : SmoothPath 𝓘(ℝ, ℂ) X)

private lemma chartBallSourcePreimage_pullback_isOpen (q : X) :
    IsOpen (γ.ambient ⁻¹' chartBallSourcePreimage q) :=
  (chartBallSourcePreimage_isOpen q).preimage γ.ambient_contMDiff.continuous

private lemma t_mem_chartBall_preimage_at_ambient (t : ℝ) :
    t ∈ γ.ambient ⁻¹' chartBallSourcePreimage (γ.ambient t) :=
  chartBallSourcePreimage_mem_self _

private lemma chartBall_preimage_cover :
    (Set.univ : Set ℝ) ⊆
      ⋃ q : X, γ.ambient ⁻¹' chartBallSourcePreimage q := fun t _ =>
  Set.mem_iUnion.mpr ⟨γ.ambient t, t_mem_chartBall_preimage_at_ambient γ t⟩

/-! ## Lebesgue radius on `Icc 0 1` -/

/-- **Lebesgue radius for the chart-ball pullback cover on `Icc 0 1`.**
For every smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) X`, there is `δ > 0` such
that for every `t ∈ Icc 0 1` there is an anchor `q : X` with the
`δ`-ball around `t` (in `ℝ`) contained in
`γ.ambient ⁻¹' chartBallSourcePreimage q`. -/
theorem smoothPath_chart_ball_anchor_cover :
    ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ q : X,
      Metric.ball t δ ⊆ γ.ambient ⁻¹' chartBallSourcePreimage q := by
  have hcover_Icc : (Set.Icc (0 : ℝ) 1) ⊆
      ⋃ q : X, γ.ambient ⁻¹' chartBallSourcePreimage q :=
    (Set.subset_univ _).trans (chartBall_preimage_cover γ)
  obtain ⟨V, hV_uni, hV_ball⟩ :=
    lebesgue_number_lemma (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      (fun q => chartBallSourcePreimage_pullback_isOpen γ q) hcover_Icc
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_uniformity_dist.mp hV_uni
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  obtain ⟨q_t, hq_t_sub⟩ := hV_ball t ht
  refine ⟨q_t, fun y hy => ?_⟩
  have h_dist : dist t y < δ := by
    rw [Metric.mem_ball] at hy; rwa [dist_comm]
  exact hq_t_sub (hδ_sub h_dist)

/-! ## Equidistant `Fin N` partition with per-segment chart-ball anchors -/

/-- **Chart-ball anchor equidistant partition.** For every smooth path
`γ : SmoothPath 𝓘(ℝ, ℂ) X` on a complex 1-manifold, there exist `N : ℕ`
with `0 < N` and chart anchors `qs : Fin N → X` such that for every
`k : Fin N` and every `s ∈ ℝ` with `(k : ℝ) / N ≤ s ≤ ((k : ℝ) + 1) / N`,
`γ.ambient s ∈ chartBallSourcePreimage (qs k)`.

Concretely, this means `γ.ambient s` lies in `(chartAt ℂ (qs k)).source`
and its chart-image lies in the canonical chart-ball at `qs k`. -/
theorem exists_chartBall_anchor_partition :
    ∃ N : ℕ, 0 < N ∧ ∃ qs : Fin N → X,
      ∀ (k : Fin N) (s : ℝ),
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ chartBallSourcePreimage (qs k) := by
  -- Step 1: Lebesgue radius δ > 0.
  obtain ⟨δ, hδ_pos, hball⟩ := smoothPath_chart_ball_anchor_cover γ
  -- Step 2: pick N ≥ 1 with 1/N < δ.
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  let N : ℕ := max M 1
  have hN_pos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hN_cast_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have h_inv_delta_pos : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδ_pos
  have hM_cast_pos : (0 : ℝ) < M := lt_trans h_inv_delta_pos hM
  have h_one_lt_M_delta : (1 : ℝ) < M * δ := (div_lt_iff₀ hδ_pos).mp hM
  have h_inv_M_lt : (1 : ℝ) / M < δ := by
    rw [div_lt_iff₀ hM_cast_pos]; linarith
  have hN_ge_M : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left _ _
  have hN_inv : (1 : ℝ) / N < δ := by
    have h_le : (1 : ℝ) / N ≤ 1 / M :=
      one_div_le_one_div_of_le hM_cast_pos hN_ge_M
    linarith
  -- Step 3: midpoint c_k = (2k+1)/(2N) ∈ Icc 0 1.
  have h_ck_in_Icc : ∀ k : Fin N, ((2 * (k : ℝ) + 1) / (2 * N)) ∈
      Set.Icc (0 : ℝ) 1 := by
    intro k
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one (by positivity)]
      have hk : (k : ℕ) + 1 ≤ N := k.isLt
      have hk_real : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
      linarith
  -- Step 4: pick a chart anchor q_k via the Lebesgue lemma at c_k.
  classical
  let qs : Fin N → X := fun k =>
    Classical.choose (hball _ (h_ck_in_Icc k))
  have hqs_spec : ∀ k : Fin N,
      Metric.ball ((2 * (k : ℝ) + 1) / (2 * N)) δ ⊆
        γ.ambient ⁻¹' chartBallSourcePreimage (qs k) := fun k =>
    Classical.choose_spec (hball _ (h_ck_in_Icc k))
  refine ⟨N, hN_pos, qs, ?_⟩
  intro k s hs_lower hs_upper
  -- Show s ∈ ball c_k δ, then apply hqs_spec.
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
  exact hqs_spec k h_in_ball

end JacobianChallenge

end
