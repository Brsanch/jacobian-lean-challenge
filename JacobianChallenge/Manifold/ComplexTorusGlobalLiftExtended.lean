/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftSmoothOnIcc

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # `pwLiftGlobal` smooth on an open nbhd of `Icc 0 1`

The closing-arc preparation. Builds `∃ δ > 0,
ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ) ∞ (pwLiftGlobal L xs γ N) (Set.Ioo (-δ) (1 + δ))`
via explicit construction of `δ` from the chart-preimage openness
radii at `xs 0` and `xs (N - 1)`.

This `δ` is needed for the final bump-multiplier discharge of
`SmoothPathLiftHypothesisTorus L`: with `pwLiftGlobal` smooth on the
open `Ioo (-δ) (1 + δ)`, multiplying by a bump that's `1` on
`Icc 0 1` and supported on `Icc (-δ/2) (1 + δ/2)` yields a globally
smooth function on `ℝ` equal to `pwLiftGlobal` on `Icc 0 1`.

## What this file ships

* `ComplexTorus.exists_extended_smooth_radius` — `∃ δ > 0,
  ContMDiffOn ... (Ioo (-δ) (1 + δ))`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Auxiliary: `pwLiftPiece k` is `ContMDiffOn` on its full chart preimage -/

private theorem pwLiftPiece_contMDiffOn_chartPreimage
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N k : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N k)
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs k)).symm.source) := by
  have h_chart : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (localChart L (discRadius_separates L) (xs k)).symm
          (γ.ambient t))
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs k)).symm.source) :=
    chartComp_contMDiffOn L γ (xs k)
  have h_eq : (pwLiftPiece L xs γ N k) = fun t =>
      (localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t)
      + cumulativeShift L xs γ N k := by
    funext t; rfl
  rw [h_eq]
  exact h_chart.add contMDiffOn_const

/-! ## Existence of a positive radius for extended smoothness -/

/-- **Extended smoothness radius**: there exists `δ > 0` such that
`pwLiftGlobal` is `ContMDiffOn` on `Set.Ioo (-δ) (1 + δ)`. -/
theorem exists_extended_smooth_radius
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ∃ δ > 0, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (-δ) (1 + δ)) := by
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_real_one_le : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h_one_div_N_pos : (0 : ℝ) < 1 / N := by positivity
  have h_one_div_N_le_one : (1 : ℝ) / N ≤ 1 := by
    rw [div_le_one hN_real_pos]; exact hN_real_one_le
  -- (A) Get ε_zero such that ContMDiffOn pwLiftGlobal (Ioo (-ε_zero) ε_zero).
  -- This mirrors pwLiftGlobal_contMDiffAt_zero's internal construction.
  have h_piece_smooth_0 :=
    pwLiftPiece_contMDiffOn_chartPreimage L xs γ N 0
  have h_zero_in_pre : (0 : ℝ) ∈ γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs 0)).symm.source :=
    h_partition 0 hN 0 (by push_cast; simp) (by push_cast; positivity)
  have h_pre_0_open : IsOpen (γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs 0)).symm.source) :=
    (((localChart L (discRadius_separates L) (xs 0)).symm).open_source).preimage
      γ.ambient_contMDiff.continuous
  rcases Metric.isOpen_iff.mp h_pre_0_open 0 h_zero_in_pre with
    ⟨ε_pre_0, hε_pre_0_pos, hε_pre_0_sub⟩
  set ε_zero : ℝ := min ε_pre_0 (1 / N) with hε_zero_def
  have hε_zero_pos : 0 < ε_zero := lt_min hε_pre_0_pos h_one_div_N_pos
  have hε_zero_le_pre : ε_zero ≤ ε_pre_0 := min_le_left _ _
  have hε_zero_le_inv_N : ε_zero ≤ 1 / N := min_le_right _ _
  have hε_zero_le_one : ε_zero ≤ 1 := le_trans hε_zero_le_inv_N h_one_div_N_le_one
  -- pwLiftGlobal = pwLiftPiece 0 on Ioo (-ε_zero) ε_zero.
  have h_eqOn_zero : Set.EqOn (pwLiftGlobal L xs γ N) (pwLiftPiece L xs γ N 0)
      (Set.Ioo (-ε_zero) ε_zero) := by
    intro t ht
    show pwLiftPiece L xs γ N (whichPiece N t) t = pwLiftPiece L xs γ N 0 t
    -- whichPiece N t = 0.
    have h_t_lt : t < ε_zero := ht.2
    have h_whichPiece_zero : whichPiece N t = 0 := by
      unfold whichPiece
      by_cases h_le : t ≤ 0
      · rw [if_pos h_le]
      · push_neg at h_le
        rw [if_neg (not_le.mpr h_le)]
        have h_t_lt_one : t < 1 := lt_of_lt_of_le h_t_lt hε_zero_le_one
        rw [if_neg (not_le.mpr h_t_lt_one)]
        have h_tN_lt_one : t * N < 1 := by
          have h1 : t < 1 / N := lt_of_lt_of_le h_t_lt hε_zero_le_inv_N
          have := (lt_div_iff₀ hN_real_pos).mp h1
          linarith
        have h_floor_zero : ⌊t * N⌋₊ = 0 :=
          Nat.floor_eq_zero.mpr h_tN_lt_one
        rw [h_floor_zero]; omega
    rw [h_whichPiece_zero]
  have h_Ioo_zero_in_pre : Set.Ioo (-ε_zero) ε_zero ⊆
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs 0)).symm.source := by
    intro t ht
    apply hε_pre_0_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [ht.1, ht.2]
  have h_zero_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (-ε_zero) ε_zero) :=
    (h_piece_smooth_0.mono h_Ioo_zero_in_pre).congr (fun y hy => h_eqOn_zero hy)
  -- (B) Get ε_one such that ContMDiffOn pwLiftGlobal (Ioo (1 - ε_one) (1 + ε_one)).
  have hNm1_lt : N - 1 < N := Nat.sub_lt hN Nat.one_pos
  have h_Nm1_eq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]; push_cast; ring
  have h_Nm1_div_eq : ((N - 1 : ℕ) : ℝ) / N = 1 - 1 / N := by
    rw [h_Nm1_eq]; field_simp
  have h_Nm1_plus_one_div_eq : (((N - 1 : ℕ) : ℝ) + 1) / N = 1 := by
    rw [h_Nm1_eq]; field_simp; ring
  have h_piece_smooth_Nm1 :=
    pwLiftPiece_contMDiffOn_chartPreimage L xs γ N (N - 1)
  have h_one_in_pre_Nm1 : (1 : ℝ) ∈ γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs (N - 1))).symm.source := by
    apply h_partition (N - 1) hNm1_lt 1
    · rw [h_Nm1_div_eq]; linarith
    · rw [h_Nm1_plus_one_div_eq]
  have h_pre_Nm1_open : IsOpen (γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs (N - 1))).symm.source) :=
    (((localChart L (discRadius_separates L) (xs (N - 1))).symm).open_source).preimage
      γ.ambient_contMDiff.continuous
  rcases Metric.isOpen_iff.mp h_pre_Nm1_open 1 h_one_in_pre_Nm1 with
    ⟨ε_pre_1, hε_pre_1_pos, hε_pre_1_sub⟩
  set ε_one : ℝ := min ε_pre_1 (1 / N) with hε_one_def
  have hε_one_pos : 0 < ε_one := lt_min hε_pre_1_pos h_one_div_N_pos
  have hε_one_le_pre : ε_one ≤ ε_pre_1 := min_le_left _ _
  have hε_one_le_inv_N : ε_one ≤ 1 / N := min_le_right _ _
  have h_eqOn_one : Set.EqOn (pwLiftGlobal L xs γ N) (pwLiftPiece L xs γ N (N - 1))
      (Set.Ioo (1 - ε_one) (1 + ε_one)) := by
    intro t ht
    show pwLiftPiece L xs γ N (whichPiece N t) t = pwLiftPiece L xs γ N (N - 1) t
    have h_t_lower : 1 - ε_one < t := ht.1
    have h_t_upper : t < 1 + ε_one := ht.2
    have ht_pos : 0 < t := by linarith
    have h_whichPiece_Nm1 : whichPiece N t = N - 1 := by
      unfold whichPiece
      rw [if_neg (not_le.mpr ht_pos)]
      by_cases h_ge : 1 ≤ t
      · rw [if_pos h_ge]
      · push_neg at h_ge
        rw [if_neg (not_le.mpr h_ge)]
        have h_t_gt_Nm1_div : ((N - 1 : ℕ) : ℝ) / N < t := by
          rw [h_Nm1_div_eq]; linarith
        have h_tN_gt : ((N - 1 : ℕ) : ℝ) < t * N := by
          have := (div_lt_iff₀ hN_real_pos).mp h_t_gt_Nm1_div
          linarith
        have h_tN_lt : t * N < N := by nlinarith
        have h_tN_nn : 0 ≤ t * N := by positivity
        have h_floor_lb : N - 1 ≤ ⌊t * N⌋₊ := by
          apply Nat.le_floor; push_cast; exact h_tN_gt.le
        have h_floor_ub : ⌊t * N⌋₊ < N := by
          rw [Nat.floor_lt h_tN_nn]; push_cast; exact h_tN_lt
        have h_floor_eq : ⌊t * N⌋₊ = N - 1 := by omega
        rw [h_floor_eq]; exact min_self _
    rw [h_whichPiece_Nm1]
  have h_Ioo_one_in_pre : Set.Ioo (1 - ε_one) (1 + ε_one) ⊆
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs (N - 1))).symm.source := by
    intro t ht
    apply hε_pre_1_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [ht.1, ht.2]
  have h_one_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (1 - ε_one) (1 + ε_one)) :=
    (h_piece_smooth_Nm1.mono h_Ioo_one_in_pre).congr (fun y hy => h_eqOn_one hy)
  -- (C) Interior smoothness on Ioo 0 1.
  have h_interior : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (0 : ℝ) 1) :=
    pwLiftGlobal_contMDiffOn_Ioo01 L xs γ h_src N hN h_partition
  -- (D) Define δ := min ε_zero ε_one. Show ContMDiffOn (Ioo (-δ) (1 + δ)).
  set δ : ℝ := min ε_zero ε_one with hδ_def
  have hδ_pos : 0 < δ := lt_min hε_zero_pos hε_one_pos
  have hδ_le_zero : δ ≤ ε_zero := min_le_left _ _
  have hδ_le_one : δ ≤ ε_one := min_le_right _ _
  refine ⟨δ, hδ_pos, ?_⟩
  -- Ioo (-δ) (1 + δ) ⊆ Ioo (-ε_zero) ε_zero ∪ Ioo 0 1 ∪ Ioo (1 - ε_one) (1 + ε_one).
  -- Use locality.
  apply contMDiffOn_of_locally_contMDiffOn
  intro t ht
  -- ht : t ∈ Ioo (-δ) (1 + δ). Find an open u ∋ t with ContMDiffOn pwLiftGlobal (Ioo ∩ u).
  by_cases h_t_neg : t < ε_zero
  · -- t < ε_zero. Use Ioo (-δ) ε_zero ⊆ Ioo (-ε_zero) ε_zero.
    refine ⟨Set.Ioo (-ε_zero) ε_zero, isOpen_Ioo, ?_, ?_⟩
    · constructor
      · linarith [ht.1, hδ_le_zero]
      · exact h_t_neg
    · exact h_zero_smooth.mono (Set.inter_subset_right)
  · push_neg at h_t_neg
    by_cases h_t_high : 1 - ε_one < t
    · -- ε_zero ≤ t. If also t > 1 - ε_one, t ∈ Ioo (1 - ε_one) (1 + ε_one).
      refine ⟨Set.Ioo (1 - ε_one) (1 + ε_one), isOpen_Ioo, ?_, ?_⟩
      · constructor
        · exact h_t_high
        · linarith [ht.2, hδ_le_one]
      · exact h_one_smooth.mono (Set.inter_subset_right)
    · -- ε_zero ≤ t ≤ 1 - ε_one. So t ∈ [ε_zero, 1 - ε_one] ⊆ Ioo 0 1.
      push_neg at h_t_high
      have h_t_pos : 0 < t := lt_of_lt_of_le hε_zero_pos h_t_neg
      have h_t_lt_one : t < 1 := by
        have : t ≤ 1 - ε_one := h_t_high
        linarith [hε_one_pos]
      refine ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo, ⟨h_t_pos, h_t_lt_one⟩, ?_⟩
      exact h_interior.mono Set.inter_subset_right

end ComplexTorus

end JacobianChallenge

end
