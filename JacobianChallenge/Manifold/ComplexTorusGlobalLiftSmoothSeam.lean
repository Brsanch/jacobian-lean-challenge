/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftSmoothInterior

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Smoothness of `pwLiftGlobal` at interior seam points

At a seam `t₀ := (k+1)/N` with `0 ≤ k` and `k + 1 < N`, the piece index
`whichPiece N t` can take two values near `t₀`:

* `t > t₀` (slightly): `whichPiece = k + 1` (since `⌊t·N⌋₊ = k + 1`);
* `t = t₀`: `whichPiece = k + 1` (since `⌊(k+1)⌋₊ = k + 1` and the
  `min` clips at `N - 1 ≥ k + 1`);
* `t < t₀` (slightly): `whichPiece = k` (since `⌊t·N⌋₊ = k`).

Hence on a small Ioo around `t₀`, `pwLiftGlobal` is either
`pwLiftPiece k` (left side) or `pwLiftPiece (k+1)` (at-and-right).

By `pwLiftPiece_eqOn_seam_nbhd`, the two coincide on an open nbhd of
`t₀`. Therefore `pwLiftGlobal` locally equals `pwLiftPiece (k+1)`,
which is smooth on its chart-source preimage (an open set containing
`t₀`).

## What this file ships

* `ComplexTorus.pwLiftGlobal_contMDiffAt_seam` — smoothness of
  `pwLiftGlobal` at an interior seam `(k+1)/N` with `k + 1 < N`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Auxiliary: `whichPiece` at the seam and just below it -/

private lemma whichPiece_at_seam
    (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : k + 1 < N) :
    whichPiece N (((k : ℝ) + 1) / N) = k + 1 := by
  -- Apply whichPiece_eq_of_Ioo_subInterval at index (k+1) — but t = (k+1)/N is
  -- the LEFT endpoint of Ioo ((k+1)/N) ((k+2)/N), not interior. Need a direct calc.
  unfold whichPiece
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_real_one_le : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- (k+1)/N > 0 since k+1 ≥ 1.
  have ht_pos : 0 < ((k : ℝ) + 1) / N := by positivity
  -- (k+1)/N < 1 since k+1 < N.
  have ht_lt_one : ((k : ℝ) + 1) / N < 1 := by
    rw [div_lt_one hN_real_pos]
    have : (k + 1 : ℕ) < N := hk
    exact_mod_cast this
  rw [if_neg (not_le.mpr ht_pos), if_neg (not_le.mpr ht_lt_one)]
  -- min ⌊(k+1)/N · N⌋₊ (N - 1).
  -- (k+1)/N · N = k+1 (since N ≠ 0).
  have h_calc : ((k : ℝ) + 1) / N * N = (k : ℝ) + 1 := by
    field_simp
  have h_floor : ⌊((k : ℝ) + 1) / N * N⌋₊ = k + 1 := by
    rw [h_calc]
    -- ⌊(k+1 : ℝ)⌋₊ = k + 1. Use the natCast form.
    have h_eq : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h_eq]
    exact Nat.floor_natCast (k + 1)
  rw [h_floor]
  -- min (k+1) (N-1) = k+1 since k+1 ≤ N-1 (k+1 < N → k+1 ≤ N-1).
  have h_kp1_le_Nm1 : k + 1 ≤ N - 1 := by omega
  exact min_eq_left h_kp1_le_Nm1

/-! ## Smoothness at interior seams -/

/-- **Smoothness at the interior seam `(k+1)/N`** (with `k + 1 < N`).
On a small open nbhd of the seam, `pwLiftGlobal` agrees with
`pwLiftPiece (k+1)` (by local agreement on the left and trivially on
the right), which is smooth on its chart-source preimage. -/
theorem pwLiftGlobal_contMDiffAt_seam
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source)
    (k : ℕ) (hk : k + 1 < N) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) (((k : ℝ) + 1) / N) := by
  set t₀ : ℝ := ((k : ℝ) + 1) / N with ht₀_def
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  -- Step 1: local agreement gives ε_LA > 0 with pwLiftPiece k = pwLiftPiece (k+1) on Ioo (t₀ - ε_LA) (t₀ + ε_LA).
  obtain ⟨ε_LA, hε_LA_pos, h_LA⟩ :=
    pwLiftPiece_eqOn_seam_nbhd L xs γ h_src N hN k hk h_partition
  -- Step 2: pwLiftPiece (k+1) is ContMDiffOn on Icc ((k+1)/N) ((k+2)/N) ⊆
  -- chartPreimage(k+1). On a slightly larger open Ioo, smoothness extends.
  -- Specifically, we want pwLiftPiece (k+1) smooth on an open nbhd of t₀.
  -- chartPreimage(k+1) is open and contains [(k+1)/N, (k+2)/N], so contains t₀.
  -- pwLiftPiece (k+1) is ContMDiffOn the open chartPreimage(k+1).
  have h_piece_full_open : IsOpen (γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs (k+1))).symm.source) := by
    apply IsOpen.preimage γ.ambient_contMDiff.continuous
    exact (localChart L (discRadius_separates L) (xs (k+1))).symm.open_source
  -- pwLiftPiece (k+1) is ContMDiffOn this full open set.
  have h_piece_full_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N (k+1))
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs (k+1))).symm.source) := by
    -- pwLiftPiece (k+1) = chart-symm composition + const shift.
    have h_chart : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
        (fun t : ℝ => (localChart L (discRadius_separates L) (xs (k+1))).symm
            (γ.ambient t))
        (γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs (k+1))).symm.source) :=
      chartComp_contMDiffOn L γ (xs (k+1))
    -- Adding a constant.
    have h_eq : (pwLiftPiece L xs γ N (k+1)) = fun t =>
        (localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient t)
        + cumulativeShift L xs γ N (k+1) := by
      funext t; rfl
    rw [h_eq]
    exact h_chart.add contMDiffOn_const
  -- Step 3: t₀ ∈ chartPreimage(k+1).
  have h_t₀_in_pre : t₀ ∈ γ.ambient ⁻¹'
      (localChart L (discRadius_separates L) (xs (k+1))).symm.source := by
    apply h_partition (k+1) hk t₀
    · rw [ht₀_def]; push_cast; linarith
    · rw [ht₀_def]; apply div_le_div_of_nonneg_right _ hN_real_pos.le
      push_cast; linarith
  -- Step 4: Pick ε > 0 with Ioo (t₀ - ε) (t₀ + ε) ⊆ chartPreimage(k+1) ∩ ⊆ Ioo for whichPiece in {k, k+1}.
  rcases Metric.isOpen_iff.mp h_piece_full_open t₀ h_t₀_in_pre with ⟨ε_chart, hε_chart_pos, hε_chart_sub⟩
  -- We also need Ioo (t₀ - ε) (t₀ + ε) to ensure whichPiece N t ∈ {k, k+1}. This requires:
  -- (a) t > 0 (so the first branch of whichPiece is skipped): t₀ - ε > 0, i.e., ε < t₀.
  -- (b) t < 1 (so the second branch is skipped): t₀ + ε < 1, i.e., ε < 1 - t₀.
  -- (c) ⌊t·N⌋₊ ∈ {k, k+1}: t·N ∈ (k, k+2), i.e., t ∈ (k/N, (k+2)/N).
  --     t₀ ± ε ∈ (k/N, (k+2)/N), so ε < 1/N.
  -- Pick ε := min (min (min ε_LA ε_chart) t₀) (min (1 - t₀) (1/N)).
  have ht₀_pos : 0 < t₀ := by rw [ht₀_def]; positivity
  have ht₀_lt_one : t₀ < 1 := by
    rw [ht₀_def, div_lt_one hN_real_pos]
    have : (k + 1 : ℕ) < N := hk
    exact_mod_cast this
  have h_one_div_N_pos : (0 : ℝ) < 1 / N := by positivity
  set ε : ℝ := min (min (min ε_LA ε_chart) t₀) (min (1 - t₀) (1 / N)) with hε_def
  have hε_pos : 0 < ε := by
    refine lt_min (lt_min (lt_min hε_LA_pos hε_chart_pos) ht₀_pos) ?_
    exact lt_min (by linarith) h_one_div_N_pos
  -- Step 5: On Ioo (t₀ - ε) (t₀ + ε), pwLiftGlobal = pwLiftPiece (k+1).
  -- And the Ioo is open and contains t₀. Use ContMDiffOn on an open set → ContMDiffAt at interior.
  have h_Ioo_in_chart : Set.Ioo (t₀ - ε) (t₀ + ε) ⊆
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs (k+1))).symm.source := by
    intro t ht
    apply hε_chart_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    refine ⟨?_, ?_⟩
    · have : ε ≤ ε_chart := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
      linarith [ht.1, ht.2]
    · have : ε ≤ ε_chart := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
      linarith [ht.1, ht.2]
  -- Equation: pwLiftGlobal = pwLiftPiece (k+1) on the small Ioo.
  have h_eqOn : Set.EqOn (pwLiftGlobal L xs γ N) (pwLiftPiece L xs γ N (k+1))
      (Set.Ioo (t₀ - ε) (t₀ + ε)) := by
    intro t ht
    -- whichPiece N t ∈ {k, k+1}.
    -- Case A: t = t₀. whichPiece = k+1 by whichPiece_at_seam, direct.
    -- Case B: t > t₀. Then t ∈ Ioo (t₀) (t₀ + ε), and t ∈ Ioo ((k+1)/N) ((k+2)/N) for small ε.
    -- Then whichPiece = k+1 by whichPiece_eq_of_Ioo_subInterval. Direct.
    -- Case C: t < t₀. Then t ∈ Ioo (t₀ - ε) (t₀), and t ∈ Ioo (k/N) ((k+1)/N) for small ε.
    -- Then whichPiece = k. Use local agreement: pwLiftPiece k = pwLiftPiece (k+1) on Ioo (t₀ - ε_LA) (t₀ + ε_LA).
    -- Since ε ≤ ε_LA, t ∈ Ioo (t₀ - ε_LA) (t₀ + ε_LA), so equality holds.
    show pwLiftPiece L xs γ N (whichPiece N t) t = pwLiftPiece L xs γ N (k+1) t
    have hε_le_LA : ε ≤ ε_LA :=
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have hε_le_t₀ : ε ≤ t₀ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hε_le_one_minus_t₀ : ε ≤ 1 - t₀ :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hε_le_inv_N : ε ≤ 1 / N :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have ht_lower : t₀ - ε < t := ht.1
    have ht_upper : t < t₀ + ε := ht.2
    have ht_pos : 0 < t := by linarith
    have ht_lt_one : t < 1 := by linarith
    -- whichPiece N t = min ⌊t·N⌋₊ (N - 1).
    -- ⌊t·N⌋₊ ∈ {k, k+1}: t·N ∈ (k, k+2).
    -- Lower: t > t₀ - ε ≥ t₀ - 1/N = (k+1)/N - 1/N = k/N. So t·N > k.
    have h_tN_gt_k : (k : ℝ) < t * N := by
      have h1 : t > t₀ - 1 / N := by linarith
      have h2 : t₀ - 1 / N = (k : ℝ) / N := by
        rw [ht₀_def]; field_simp; ring
      rw [h2] at h1
      have := (div_lt_iff₀ hN_real_pos).mp h1
      linarith
    -- Upper: t < t₀ + ε ≤ t₀ + 1/N = (k+1)/N + 1/N = (k+2)/N. So t·N < k+2.
    have h_tN_lt_kp2 : t * N < (k : ℝ) + 2 := by
      have h1 : t < t₀ + 1 / N := by linarith
      have h2 : t₀ + 1 / N = ((k : ℝ) + 2) / N := by
        rw [ht₀_def]; field_simp; ring
      rw [h2] at h1
      have := (lt_div_iff₀ hN_real_pos).mp h1
      linarith
    have h_tN_nn : 0 ≤ t * N := by positivity
    have h_floor_lb : k ≤ ⌊t * N⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact h_tN_gt_k.le
    have h_floor_ub : ⌊t * N⌋₊ < k + 2 := by
      rw [Nat.floor_lt h_tN_nn]
      push_cast; exact h_tN_lt_kp2
    have h_floor_in : ⌊t * N⌋₊ = k ∨ ⌊t * N⌋₊ = k + 1 := by omega
    have h_kp1_le_Nm1 : k + 1 ≤ N - 1 := by omega
    have hk_le_Nm1 : k ≤ N - 1 := by omega
    -- whichPiece N t = ⌊t·N⌋₊ in both cases.
    have h_whichPiece : whichPiece N t = ⌊t * N⌋₊ := by
      unfold whichPiece
      rw [if_neg (not_le.mpr ht_pos), if_neg (not_le.mpr ht_lt_one)]
      rcases h_floor_in with h_eq_k | h_eq_kp1
      · rw [h_eq_k, min_eq_left hk_le_Nm1]
      · rw [h_eq_kp1, min_eq_left h_kp1_le_Nm1]
    rw [h_whichPiece]
    rcases h_floor_in with h_eq_k | h_eq_kp1
    · -- whichPiece = k. Use local agreement (ε ≤ ε_LA).
      rw [h_eq_k]
      apply h_LA t
      refine ⟨?_, ?_⟩ <;> linarith
    · -- whichPiece = k+1. Direct.
      rw [h_eq_kp1]
  -- Step 6: pwLiftPiece (k+1) is ContMDiffOn (Ioo (t₀ - ε) (t₀ + ε)) via the chart preimage.
  have h_piece_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N (k+1))
      (Set.Ioo (t₀ - ε) (t₀ + ε)) :=
    h_piece_full_smooth.mono h_Ioo_in_chart
  -- pwLiftGlobal is ContMDiffOn the Ioo via h_eqOn.
  have h_global_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo (t₀ - ε) (t₀ + ε)) :=
    h_piece_smooth_Ioo.congr (fun y hy => h_eqOn hy)
  -- Promote ContMDiffOn on open → ContMDiffAt at interior.
  have h_t₀_in_Ioo : t₀ ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := by
    constructor <;> linarith
  exact h_global_smooth_Ioo.contMDiffAt (isOpen_Ioo.mem_nhds h_t₀_in_Ioo)

end ComplexTorus

end JacobianChallenge

end
