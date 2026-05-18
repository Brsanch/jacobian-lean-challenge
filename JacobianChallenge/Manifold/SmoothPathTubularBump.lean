/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.unusedSectionVars false

/-! # Smooth bump on `[0, 1]` + tubular-neighborhood lemma

Building blocks for the chart-N pullback discharge of
`SmoothLoopChartNPullbackExistsHypothesis`.

## What ships

* `tubularBump δ : ℝ → ℝ` — for `δ > 0`, a C^∞ bump on `ℝ` with:
  - `tubularBump δ t = 1` for `t ∈ [0, 1]`,
  - `tubularBump δ t = 0` for `t ∉ (-δ, 1 + δ)`,
  - `tubularBump δ t ∈ [0, 1]` always.

* `contDiff_tubularBump` — global C^∞-smoothness.

* `tubularBump_eq_one_of_mem_Icc` — `= 1` on `[0, 1]`.

* `tubularBump_eq_zero_outside_Ioo` — `= 0` outside `[-δ, 1 + δ]`.

* `exists_tubular_delta` — given an open set `U ⊆ ℝ` containing
  `[0, 1]`, exists `δ > 0` with `Set.Ioo (-δ) (1 + δ) ⊆ U`.

No `sorry`, no `axiom`. -/

open Set
open scoped Topology ContDiff

namespace JacobianChallenge

/-- The smooth bump `tubularBump δ t := smoothTransition ((t + δ) / δ)
   * smoothTransition ((1 + δ - t) / δ)`, parameterised by `δ > 0`. -/
noncomputable def tubularBump (δ t : ℝ) : ℝ :=
  Real.smoothTransition ((t + δ) / δ) *
    Real.smoothTransition ((1 + δ - t) / δ)

variable {δ : ℝ}

/-- C^∞-smoothness of `tubularBump δ` on `ℝ`. -/
lemma contDiff_tubularBump (hδ : 0 < δ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (tubularBump δ) := by
  unfold tubularBump
  have h_inner1 : ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => (t + δ) / δ) := by
    have h_id : ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => t) := contDiff_id
    have h_const : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ => δ) := contDiff_const
    exact (h_id.add h_const).div h_const (fun _ => hδ.ne')
  have h_inner2 : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => (1 + δ - t) / δ) := by
    have h_const : ContDiff ℝ (∞ : WithTop ℕ∞)
        (fun _ : ℝ => (1 + δ : ℝ)) := contDiff_const
    have h_id : ContDiff ℝ (∞ : WithTop ℕ∞) (fun t : ℝ => t) := contDiff_id
    have h_const_δ : ContDiff ℝ (∞ : WithTop ℕ∞) (fun _ : ℝ => δ) := contDiff_const
    exact (h_const.sub h_id).div h_const_δ (fun _ => hδ.ne')
  have h_st : ContDiff ℝ (∞ : WithTop ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have h_left : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((t + δ) / δ)) :=
    h_st.comp h_inner1
  have h_right : ContDiff ℝ (∞ : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((1 + δ - t) / δ)) :=
    h_st.comp h_inner2
  exact h_left.mul h_right

/-- For `t ∈ [0, 1]` and `δ > 0`, `tubularBump δ t = 1`.

Proof: both `(t + δ)/δ ≥ 1` (since `t ≥ 0`, so `t + δ ≥ δ`) and
`(1 + δ - t)/δ ≥ 1` (since `t ≤ 1`, so `1 + δ - t ≥ δ`), so both
`smoothTransition` factors equal `1`. -/
lemma tubularBump_eq_one_of_mem_Icc (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    tubularBump δ t = 1 := by
  unfold tubularBump
  obtain ⟨ht0, ht1⟩ := ht
  have h_left : Real.smoothTransition ((t + δ) / δ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hδ]
    linarith
  have h_right : Real.smoothTransition ((1 + δ - t) / δ) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hδ]
    linarith
  rw [h_left, h_right]
  ring

/-- For `t ≤ -δ` (with `δ > 0`), the left factor of `tubularBump δ` is `0`,
hence `tubularBump δ t = 0`. -/
lemma tubularBump_eq_zero_of_le_neg_delta (hδ : 0 < δ) {t : ℝ} (ht : t ≤ -δ) :
    tubularBump δ t = 0 := by
  unfold tubularBump
  have h_left : Real.smoothTransition ((t + δ) / δ) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have h_num : t + δ ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h_num hδ.le
  rw [h_left]
  ring

/-- For `t ≥ 1 + δ` (with `δ > 0`), the right factor of `tubularBump δ` is `0`. -/
lemma tubularBump_eq_zero_of_ge_one_add_delta (hδ : 0 < δ) {t : ℝ} (ht : 1 + δ ≤ t) :
    tubularBump δ t = 0 := by
  unfold tubularBump
  have h_right : Real.smoothTransition ((1 + δ - t) / δ) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have h_num : 1 + δ - t ≤ 0 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg h_num hδ.le
  rw [h_right]
  ring

/-- `tubularBump δ t ∈ [0, 1]` for all `t`. -/
lemma tubularBump_mem_Icc {t : ℝ} : tubularBump δ t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold tubularBump
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · calc Real.smoothTransition ((t + δ) / δ) *
            Real.smoothTransition ((1 + δ - t) / δ)
        ≤ 1 * 1 := by
          apply mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
          · exact Real.smoothTransition.nonneg _
          · exact zero_le_one
      _ = 1 := one_mul 1

/-! ## Tubular-neighborhood existence -/

/-- **Tubular-neighborhood lemma.** Given an open `U ⊆ ℝ` containing
the closed interval `[0, 1]`, there exists `δ > 0` such that
`Ioo (-δ) (1 + δ) ⊆ U`.

Proof: openness gives `ε₀ > 0` with `Ioo (-ε₀) ε₀ ⊆ U` at `0`, and
`ε₁ > 0` with `Ioo (1 - ε₁) (1 + ε₁) ⊆ U` at `1`. Take
`δ := min (min ε₀ ε₁) (1/2)`. Then `Ioo (-δ) (1 + δ)` decomposes
into `Ioo (-δ) 0 ∪ Icc 0 1 ∪ Ioo 1 (1 + δ)`, each in `U`. -/
lemma exists_tubular_delta {U : Set ℝ} (hU_open : IsOpen U)
    (hU_Icc : Set.Icc (0 : ℝ) 1 ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Set.Ioo (-δ) (1 + δ) ⊆ U := by
  -- 0 ∈ U.
  have h0 : (0 : ℝ) ∈ U := hU_Icc ⟨le_refl 0, zero_le_one⟩
  -- 1 ∈ U.
  have h1 : (1 : ℝ) ∈ U := hU_Icc ⟨zero_le_one, le_refl 1⟩
  -- Open neighborhood at 0.
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.isOpen_iff.mp hU_open 0 h0
  obtain ⟨ε₁, hε₁_pos, hε₁_sub⟩ := Metric.isOpen_iff.mp hU_open 1 h1
  refine ⟨min (min ε₀ ε₁) (1/2), ?_, ?_⟩
  · -- δ > 0.
    refine lt_min ?_ (by norm_num)
    exact lt_min hε₀_pos hε₁_pos
  · -- The inclusion.
    intro t ⟨ht_lo, ht_hi⟩
    set δ := min (min ε₀ ε₁) (1/2) with hδ_def
    have hδ_pos : 0 < δ := lt_min (lt_min hε₀_pos hε₁_pos) (by norm_num)
    have hδ_le_ε₀ : δ ≤ ε₀ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ_le_ε₁ : δ ≤ ε₁ := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ_le_half : δ ≤ 1/2 := min_le_right _ _
    -- Case 1: t < 0. Then |t - 0| = -t < δ ≤ ε₀, so t ∈ ball 0 ε₀ ⊆ U.
    -- Case 2: 0 ≤ t ≤ 1. Then t ∈ Icc 0 1 ⊆ U.
    -- Case 3: t > 1. Then |t - 1| = t - 1 < δ ≤ ε₁, so t ∈ ball 1 ε₁ ⊆ U.
    by_cases h_lt0 : t < 0
    · apply hε₀_sub
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith : t - 0 ≤ 0)]
      linarith
    · push_neg at h_lt0  -- h_lt0 : 0 ≤ t
      by_cases h_le1 : t ≤ 1
      · exact hU_Icc ⟨h_lt0, h_le1⟩
      · push_neg at h_le1  -- h_le1 : 1 < t
        apply hε₁_sub
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < t - 1)]
        linarith

end JacobianChallenge
