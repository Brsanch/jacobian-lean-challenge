/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftSmoothSeam

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # `pwLiftGlobal` is `ContMDiff` on the open interval `Ioo 0 1`

Combines `pwLiftGlobal_contMDiffAt_interior` (smoothness on the open
sub-intervals `Ioo (k/N) ((k+1)/N)`) and `pwLiftGlobal_contMDiffAt_seam`
(smoothness at the interior seams `(k+1)/N`) into a single statement:

  `ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) (Set.Ioo 0 1)`.

Every `t ∈ Ioo 0 1` is either in some piece interior or at an interior
seam, and both cases land `ContMDiffAt`. `ContMDiffOn` follows.

## What this file ships

* `ComplexTorus.pwLiftGlobal_contMDiffOn_Ioo01` — smoothness on
  `Ioo 0 1`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Smoothness on `Ioo 0 1` -/

/-- **`pwLiftGlobal` is `ContMDiffOn` on `Ioo 0 1`** under the
chart-anchor partition hypothesis. Every interior point is either in a
piece interior or at an interior seam; both cases land smoothness. -/
theorem pwLiftGlobal_contMDiffOn_Ioo01
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  -- For each t ∈ Ioo 0 1, find a piece index k. Either t = (k+1)/N (a seam) or
  -- t lies strictly inside Ioo (k/N) ((k+1)/N).
  -- Use: there exists k < N with t ∈ Icc (k/N) ((k+1)/N). Specifically,
  -- k := whichPiece N t. Then either t = (k+1)/N (seam at the upper endpoint, k+1 < N)
  -- or t ∈ Ioo (k/N) ((k+1)/N) (interior of piece k).
  -- Wait — at t = k/N (lower endpoint of piece k for k > 0), it's also a seam between
  -- pieces k-1 and k. Need to handle this. The seam-smoothness theorem already covers
  -- seam (k+1)/N for k+1 < N, equivalently seams at j/N for 0 < j < N.
  -- Strategy: split on whether t is a seam (j/N for some 0 < j < N) or not.
  by_cases h_seam : ∃ j : ℕ, 0 < j ∧ j < N ∧ t = (j : ℝ) / N
  · -- Seam case. Let j = k + 1 with k + 1 < N.
    obtain ⟨j, hj_pos, hj_lt, h_eq⟩ := h_seam
    -- Set k := j - 1.
    have hj_ge_one : 1 ≤ j := hj_pos
    set k : ℕ := j - 1 with hk_def
    have h_kp1_eq_j : k + 1 = j := by omega
    have h_kp1_lt : k + 1 < N := by rw [h_kp1_eq_j]; exact hj_lt
    -- Rewrite t = (k+1)/N.
    have h_t_eq : t = ((k : ℝ) + 1) / N := by
      rw [h_eq]
      congr 1
      have : ((j : ℕ) : ℝ) = (k : ℝ) + 1 := by
        have : (j : ℕ) = k + 1 := by omega
        rw [this]; push_cast; ring
      exact this
    rw [h_t_eq]
    exact (pwLiftGlobal_contMDiffAt_seam L xs γ h_src N hN h_partition k h_kp1_lt).contMDiffWithinAt
  · -- Non-seam case. Find k such that t ∈ Ioo (k/N) ((k+1)/N).
    -- whichPiece N t gives a candidate k. We need to show t is in the open sub-interval.
    -- Either t < (whichPiece+1)/N strictly (non-seam) or t = (whichPiece+1)/N (seam, contradiction).
    -- And t > whichPiece/N strictly (otherwise t = whichPiece/N which is a seam if whichPiece > 0,
    -- or t = 0 contradicting t ∈ Ioo 0 1 if whichPiece = 0).
    push_neg at h_seam
    set k : ℕ := whichPiece N t with hk_def
    have hk_lt : k < N := whichPiece_lt_of_Icc01 N hN t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    -- t > k/N strictly. By piece-membership, k/N ≤ t.
    have h_t_lower : (k : ℝ) / N ≤ t :=
      (t_in_whichPiece_subInterval N hN t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).1
    -- If t = k/N, then either k = 0 (so t = 0, contradiction with ht.1) or k > 0 (so t is a
    -- seam, contradiction with h_seam).
    have h_t_gt_lower : (k : ℝ) / N < t := by
      rcases eq_or_lt_of_le h_t_lower with h_eq | h_lt
      · -- t = k/N. Case on k.
        by_cases hk_pos : 0 < k
        · -- Seam at k/N with 0 < k < N. Contradiction with h_seam.
          exfalso
          apply h_seam k hk_pos hk_lt h_eq.symm
        · -- k = 0, so t = 0, contradicting ht.1 : 0 < t.
          push_neg at hk_pos
          have hk_eq : k = 0 := Nat.le_zero.mp hk_pos
          rw [hk_eq] at h_eq
          push_cast at h_eq
          simp at h_eq
          linarith [ht.1]
      · exact h_lt
    -- t ≤ (k+1)/N. Similarly, t < (k+1)/N strictly (otherwise t is a seam at (k+1)/N).
    have h_t_upper : t ≤ ((k : ℝ) + 1) / N :=
      (t_in_whichPiece_subInterval N hN t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).2
    have h_t_lt_upper : t < ((k : ℝ) + 1) / N := by
      rcases eq_or_lt_of_le h_t_upper with h_eq | h_lt
      · -- t = (k+1)/N. Seam case unless k+1 = N (in which case t = 1, contradicting ht.2).
        by_cases h_kp1_lt_N : k + 1 < N
        · -- Seam case, contradiction with h_seam.
          exfalso
          apply h_seam (k + 1) (Nat.succ_pos k) h_kp1_lt_N
          rw [h_eq]
          push_cast; ring
        · -- k + 1 ≥ N, so k + 1 = N (since k < N), so t = 1, contradicting ht.2.
          push_neg at h_kp1_lt_N
          have h_kp1_eq_N : k + 1 = N := by omega
          have h_t_eq_one : t = 1 := by
            rw [h_eq]
            have : ((k : ℝ) + 1) = N := by
              have : (k + 1 : ℕ) = N := h_kp1_eq_N
              have h := this
              exact_mod_cast h
            rw [this]; field_simp
          linarith [ht.2]
      · exact h_lt
    -- Now t ∈ Ioo (k/N) ((k+1)/N), apply interior smoothness.
    have ht_in_Ioo : t ∈ Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N) :=
      ⟨h_t_gt_lower, h_t_lt_upper⟩
    exact (pwLiftGlobal_contMDiffAt_interior L xs γ N hN h_partition k hk_lt t
      ht_in_Ioo).contMDiffWithinAt

end ComplexTorus

end JacobianChallenge

end
