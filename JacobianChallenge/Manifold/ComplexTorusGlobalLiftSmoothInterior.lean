/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftIdentity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Smoothness of `pwLiftGlobal` at piece-interior points

For `t` in the *open* sub-interval `Ioo (k/N) ((k+1)/N)`, the piece
index `whichPiece N t` equals `k` (strict inequalities ensure
`⌊t·N⌋₊ = k` AND `min ⌊t·N⌋₊ (N-1) = k`). Hence `pwLiftGlobal` agrees
with `pwLiftPiece L xs γ N k` in a neighborhood of `t`, and inherits
its smoothness.

This is the easy half of `pwLiftGlobal` smoothness — interior of
pieces, where no piece-switching occurs. The hard half (smoothness at
seams via local agreement) lands in a follow-up chip.

## What this file ships

* `ComplexTorus.whichPiece_eq_of_Ioo_subInterval` — for `t ∈ Ioo (k/N)
  ((k+1)/N)`, `whichPiece N t = k` (under `k < N` and `0 < t`).

* `ComplexTorus.pwLiftGlobal_contMDiffAt_interior` — for `t ∈ Ioo (k/N)
  ((k+1)/N)` with `k < N`, `pwLiftGlobal` is `ContMDiffAt` at `t`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `whichPiece` reduces to `k` on open sub-intervals -/

/-- **`whichPiece N t = k` on the open sub-interval `Ioo (k/N) ((k+1)/N)`**,
under `0 < N`, `k < N`, and `k + 1 ≤ N`. The strict bounds force
`⌊t·N⌋₊ = k` and `min ⌊t·N⌋₊ (N - 1) = k`. -/
theorem whichPiece_eq_of_Ioo_subInterval
    (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : k < N) (t : ℝ)
    (ht : t ∈ Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :
    whichPiece N t = k := by
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN_real_one_le : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- t > k/N ≥ 0 (since k ≥ 0).
  have ht_lower : (k : ℝ) / N < t := ht.1
  have ht_upper : t < ((k : ℝ) + 1) / N := ht.2
  have h_k_div_nn : 0 ≤ (k : ℝ) / N := by positivity
  have ht_pos : 0 < t := lt_of_le_of_lt h_k_div_nn ht_lower
  -- t < (k+1)/N ≤ N/N = 1 (when k+1 ≤ N, i.e., k < N).
  have h_kp1_div_le_one : ((k : ℝ) + 1) / N ≤ 1 := by
    rw [div_le_one hN_real_pos]
    have hk_real : (k : ℝ) + 1 ≤ N := by
      have : (k + 1 : ℕ) ≤ N := hk
      exact_mod_cast this
    exact hk_real
  have ht_lt_one : t < 1 := lt_of_lt_of_le ht_upper h_kp1_div_le_one
  unfold whichPiece
  rw [if_neg (not_le.mpr ht_pos), if_neg (not_le.mpr ht_lt_one)]
  -- Goal: min ⌊t·N⌋₊ (N - 1) = k.
  -- From t·N > k: ⌊t·N⌋₊ ≥ k.
  -- From t·N < k + 1: ⌊t·N⌋₊ ≤ k. Hence = k.
  have h_tN_gt : (k : ℝ) < t * N := by
    have := (div_lt_iff₀ hN_real_pos).mp ht_lower
    linarith
  have h_tN_lt : t * N < (k : ℝ) + 1 := by
    have := (lt_div_iff₀ hN_real_pos).mp ht_upper
    linarith
  have h_tN_nn : 0 ≤ t * N := by positivity
  have h_floor_eq : ⌊t * N⌋₊ = k := by
    have h_lb : k ≤ ⌊t * N⌋₊ := by
      apply Nat.le_floor
      push_cast
      exact h_tN_gt.le
    have h_ub : ⌊t * N⌋₊ ≤ k := by
      have h_lt : ⌊t * N⌋₊ < k + 1 := by
        rw [Nat.floor_lt h_tN_nn]
        push_cast; exact h_tN_lt
      omega
    omega
  rw [h_floor_eq]
  have h_min_eq : min k (N - 1) = k := by
    apply min_eq_left
    omega
  exact h_min_eq

/-! ## `pwLiftGlobal` is `ContMDiffAt` on piece interiors -/

/-- **Smoothness on piece interior**: for `t ∈ Ioo (k/N) ((k+1)/N)`,
`pwLiftGlobal` is `ContMDiffAt` at `t`. -/
theorem pwLiftGlobal_contMDiffAt_interior
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source)
    (k : ℕ) (hk : k < N) (t : ℝ)
    (ht : t ∈ Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N) t := by
  -- On the open Ioo, pwLiftGlobal agrees with pwLiftPiece k (because whichPiece = k).
  -- pwLiftPiece k is smooth on the full chart-source preimage (an open set ⊇ Icc).
  -- Hence pwLiftGlobal is smooth at t.
  -- Step 1: Find an open nbhd U of t where pwLiftGlobal agrees with pwLiftPiece k.
  -- The open Ioo (k/N) ((k+1)/N) is such a U.
  have h_Ioo_open : IsOpen (Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) := isOpen_Ioo
  have h_eqOn : Set.EqOn (pwLiftGlobal L xs γ N) (pwLiftPiece L xs γ N k)
      (Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) := by
    intro t' ht'
    show pwLiftPiece L xs γ N (whichPiece N t') t' = pwLiftPiece L xs γ N k t'
    rw [whichPiece_eq_of_Ioo_subInterval N hN k hk t' ht']
  -- Step 2: pwLiftPiece k is ContMDiffOn on the chart-source preimage; Ioo is a
  -- subset (proved via the partition).
  have h_piece_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N k)
      (Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :=
    pwLiftPiece_contMDiffOn L xs γ N hN k hk h_partition
  -- Restrict to the open Ioo.
  have h_subset : Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N) ⊆
      Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N) := Set.Ioo_subset_Icc_self
  have h_piece_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N k)
      (Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :=
    h_piece_smooth.mono h_subset
  -- Step 3: ContMDiffOn on an open set → ContMDiffAt at interior points.
  have h_global_smooth_Ioo : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftGlobal L xs γ N)
      (Set.Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :=
    h_piece_smooth_Ioo.congr (fun y hy => h_eqOn hy)
  exact h_global_smooth_Ioo.contMDiffAt (h_Ioo_open.mem_nhds ht)

end ComplexTorus

end JacobianChallenge

end
