/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftSmoothOnOpen

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Smoothness of `pwLiftGlobal` at the endpoints `0` and `1`

At `t = 0` and `t = 1`, restrict to a small Ioo (avoiding the other
endpoint) and use that `whichPiece N` is constant (= `0` resp.
`N - 1`) on the small Ioo. Then `pwLiftGlobal` coincides with
`pwLiftPiece 0` resp. `pwLiftPiece (N - 1)`, which is smooth on the
relevant chart-source preimage (an open set containing the endpoint).

## What this file ships

* `ComplexTorus.pwLiftGlobal_contMDiffAt_zero` — `ContMDiffAt` at `t = 0`.

* `ComplexTorus.pwLiftGlobal_contMDiffAt_one` — `ContMDiffAt` at `t = 1`.

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

/-! ## Smoothness at `t = 0` -/

/-- **Smoothness at `t = 0`**. -/
theorem pwLiftGlobal_contMDiffAt_zero
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) 0 := by
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_real_one_le : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h_one_div_N_pos : (0 : ℝ) < 1 / N := by positivity
  have h_one_div_N_le_one : (1 : ℝ) / N ≤ 1 := by
    rw [div_le_one hN_real_pos]; exact hN_real_one_le
  -- pwLiftPiece 0 ContMDiffOn its chart preimage.
  have h_piece_smooth :=
    pwLiftPiece_contMDiffOn_chartPreimage L xs γ N 0
  have h_zero_in_pre : (0 : ℝ) ∈ γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs 0)).symm.source :=
    h_partition 0 hN 0 (by push_cast; simp) (by push_cast; positivity)
  have h_pre_open : IsOpen (γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs 0)).symm.source) :=
    (((localChart L (discRadius_separates L) (xs 0)).symm).open_source).preimage
      γ.ambient_contMDiff.continuous
  rcases Metric.isOpen_iff.mp h_pre_open 0 h_zero_in_pre with ⟨ε_pre, hε_pre_pos, hε_pre_sub⟩
  -- Pick ε ≤ min ε_pre (1/N) (so whichPiece N t = 0 for t < 1/N).
  set ε : ℝ := min ε_pre (1 / N) with hε_def
  have hε_pos : 0 < ε := lt_min hε_pre_pos h_one_div_N_pos
  have hε_le_pre : ε ≤ ε_pre := min_le_left _ _
  have hε_le_inv_N : ε ≤ 1 / N := min_le_right _ _
  have hε_le_one : ε ≤ 1 := le_trans hε_le_inv_N h_one_div_N_le_one
  -- On Ioo (-ε) ε, whichPiece N t = 0.
  have h_whichPiece_zero_on : ∀ t ∈ Set.Ioo (-ε) ε, whichPiece N t = 0 := by
    intro t ht
    unfold whichPiece
    have h_t_lt : t < ε := ht.2
    by_cases h_le : t ≤ 0
    · rw [if_pos h_le]
    · push_neg at h_le
      rw [if_neg (not_le.mpr h_le)]
      have h_t_lt_one : t < 1 := lt_of_lt_of_le h_t_lt hε_le_one
      rw [if_neg (not_le.mpr h_t_lt_one)]
      -- ⌊tN⌋₊ = 0 since t·N < 1.
      have h_tN_lt_one : t * N < 1 := by
        have h1 : t < 1 / N := lt_of_lt_of_le h_t_lt hε_le_inv_N
        have := (lt_div_iff₀ hN_real_pos).mp h1
        linarith
      have h_tN_nn : 0 ≤ t * N := by positivity
      have h_floor_zero : ⌊t * N⌋₊ = 0 := by
        apply Nat.floor_eq_zero.mpr
        exact h_tN_lt_one
      rw [h_floor_zero]
      omega
  -- pwLiftGlobal = pwLiftPiece 0 on Ioo (-ε) ε.
  have h_eqOn : Set.EqOn (pwLiftGlobal L xs γ N) (pwLiftPiece L xs γ N 0)
      (Set.Ioo (-ε) ε) := by
    intro t ht
    show pwLiftPiece L xs γ N (whichPiece N t) t = pwLiftPiece L xs γ N 0 t
    rw [h_whichPiece_zero_on t ht]
  -- Ioo (-ε) ε ⊆ chart preimage.
  have h_Ioo_in_pre : Set.Ioo (-ε) ε ⊆
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs 0)).symm.source := by
    intro t ht
    apply hε_pre_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [ht.1, ht.2]
  have h_piece_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N 0)
      (Set.Ioo (-ε) ε) := h_piece_smooth.mono h_Ioo_in_pre
  have h_global_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (-ε) ε) :=
    h_piece_smooth_Ioo.congr (fun y hy => h_eqOn hy)
  have h_zero_in_Ioo : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
  exact h_global_smooth_Ioo.contMDiffAt (isOpen_Ioo.mem_nhds h_zero_in_Ioo)

/-! ## Smoothness at `t = 1` -/

/-- **Smoothness at `t = 1`**. -/
theorem pwLiftGlobal_contMDiffAt_one
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) 1 := by
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_real_one_le : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h_one_div_N_pos : (0 : ℝ) < 1 / N := by positivity
  -- (N - 1) / N + 1/N = 1 (as reals); convert via Nat.cast_sub hN.
  have h_Nm1_eq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]; push_cast; ring
  have h_Nm1_div_eq : ((N - 1 : ℕ) : ℝ) / N = 1 - 1 / N := by
    rw [h_Nm1_eq]; field_simp
  have h_Nm1_plus_one_div_eq : (((N - 1 : ℕ) : ℝ) + 1) / N = 1 := by
    rw [h_Nm1_eq]; field_simp; ring
  have hNm1_lt : N - 1 < N := Nat.sub_lt hN Nat.one_pos
  -- pwLiftPiece (N - 1) ContMDiffOn chart preimage.
  have h_piece_smooth :=
    pwLiftPiece_contMDiffOn_chartPreimage L xs γ N (N - 1)
  have h_one_in_pre : (1 : ℝ) ∈ γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs (N - 1))).symm.source := by
    apply h_partition (N - 1) hNm1_lt 1
    · rw [h_Nm1_div_eq]; linarith
    · rw [h_Nm1_plus_one_div_eq]
  have h_pre_open : IsOpen (γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs (N - 1))).symm.source) :=
    (((localChart L (discRadius_separates L) (xs (N - 1))).symm).open_source).preimage
      γ.ambient_contMDiff.continuous
  rcases Metric.isOpen_iff.mp h_pre_open 1 h_one_in_pre with ⟨ε_pre, hε_pre_pos, hε_pre_sub⟩
  set ε : ℝ := min ε_pre (1 / N) with hε_def
  have hε_pos : 0 < ε := lt_min hε_pre_pos h_one_div_N_pos
  have hε_le_pre : ε ≤ ε_pre := min_le_left _ _
  have hε_le_inv_N : ε ≤ 1 / N := min_le_right _ _
  have hε_le_one : ε ≤ 1 := le_trans hε_le_inv_N
    (by rw [div_le_one hN_real_pos]; exact hN_real_one_le)
  -- On Ioo (1 - ε) (1 + ε), whichPiece N t = N - 1.
  have h_whichPiece_Nm1_on : ∀ t ∈ Set.Ioo (1 - ε) (1 + ε),
      whichPiece N t = N - 1 := by
    intro t ht
    unfold whichPiece
    have h_t_lower : 1 - ε < t := ht.1
    have h_t_upper : t < 1 + ε := ht.2
    have ht_pos : 0 < t := by linarith
    rw [if_neg (not_le.mpr ht_pos)]
    by_cases h_ge : 1 ≤ t
    · rw [if_pos h_ge]
    · push_neg at h_ge
      rw [if_neg (not_le.mpr h_ge)]
      -- t > 1 - ε ≥ 1 - 1/N = (N - 1)/N. So tN > N - 1.
      have h_t_gt_Nm1_div : ((N - 1 : ℕ) : ℝ) / N < t := by
        rw [h_Nm1_div_eq]; linarith
      have h_tN_gt : ((N - 1 : ℕ) : ℝ) < t * N := by
        have := (div_lt_iff₀ hN_real_pos).mp h_t_gt_Nm1_div
        linarith
      have h_tN_lt : t * N < N := by nlinarith
      have h_tN_nn : 0 ≤ t * N := by positivity
      have h_floor_lb : N - 1 ≤ ⌊t * N⌋₊ := by
        apply Nat.le_floor
        push_cast
        exact h_tN_gt.le
      have h_floor_ub : ⌊t * N⌋₊ < N := by
        rw [Nat.floor_lt h_tN_nn]
        push_cast; exact h_tN_lt
      have h_floor_eq : ⌊t * N⌋₊ = N - 1 := by omega
      rw [h_floor_eq]
      exact min_self _
  have h_eqOn : Set.EqOn (pwLiftGlobal L xs γ N) (pwLiftPiece L xs γ N (N - 1))
      (Set.Ioo (1 - ε) (1 + ε)) := by
    intro t ht
    show pwLiftPiece L xs γ N (whichPiece N t) t = pwLiftPiece L xs γ N (N - 1) t
    rw [h_whichPiece_Nm1_on t ht]
  have h_Ioo_in_pre : Set.Ioo (1 - ε) (1 + ε) ⊆
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs (N - 1))).symm.source := by
    intro t ht
    apply hε_pre_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩ <;> linarith [ht.1, ht.2]
  have h_piece_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N (N - 1))
      (Set.Ioo (1 - ε) (1 + ε)) := h_piece_smooth.mono h_Ioo_in_pre
  have h_global_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (1 - ε) (1 + ε)) :=
    h_piece_smooth_Ioo.congr (fun y hy => h_eqOn hy)
  have h_one_in_Ioo : (1 : ℝ) ∈ Set.Ioo (1 - ε) (1 + ε) := by constructor <;> linarith
  exact h_global_smooth_Ioo.contMDiffAt (isOpen_Ioo.mem_nhds h_one_in_Ioo)

end ComplexTorus

end JacobianChallenge

end
