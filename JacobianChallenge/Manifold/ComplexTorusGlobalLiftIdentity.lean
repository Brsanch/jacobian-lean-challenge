/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLift

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Piece-membership identity for `whichPiece` and the global lift identity

For `t ∈ Icc 0 1`, `t` lies in the sub-interval indexed by
`whichPiece N t`:

  `t ∈ Icc (whichPiece N t / N) ((whichPiece N t + 1) / N)`.

This is the membership identity that lets `mkQ_pwLiftPiece` apply at
`pwLiftGlobal`, yielding the lift identity `mkQ ∘ pwLiftGlobal =
γ.ambient` on `Icc 0 1`.

## What this file ships

* `ComplexTorus.t_in_whichPiece_subInterval` — for `t ∈ Icc 0 1`,
  `t ∈ Icc (whichPiece N t / N) ((whichPiece N t + 1) / N)`.

* `ComplexTorus.mkQ_pwLiftGlobal_on_Icc01` — the lift identity
  `mkQ ∘ pwLiftGlobal = γ.ambient` on `Icc 0 1`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Piece-membership identity for `whichPiece` -/

/-- **Piece membership.** For `t ∈ Icc 0 1`, `t` satisfies
`whichPiece N t / N ≤ t ≤ (whichPiece N t + 1) / N`. -/
theorem t_in_whichPiece_subInterval
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((whichPiece N t : ℝ) / N ≤ t) ∧ (t ≤ ((whichPiece N t : ℝ) + 1) / N) := by
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold whichPiece
  split_ifs with h_le h_ge
  · -- Case: t ≤ 0. Then whichPiece = 0. Need 0/N ≤ t ≤ 1/N.
    -- Combined with t ∈ Icc 0 1 (so t ≥ 0), t = 0. Hence 0 ≤ 0 and 0 ≤ 1/N.
    constructor
    · push_cast; simp
      linarith [ht.1]
    · push_cast
      rw [le_div_iff₀ hN_real_pos]
      have ht_zero : t = 0 := le_antisymm h_le ht.1
      rw [ht_zero]
      linarith
  · -- Case: t > 0, 1 ≤ t. Then whichPiece = N - 1. Need (N-1)/N ≤ t ≤ ((N-1)+1)/N = N/N = 1.
    constructor
    · push_cast
      rw [div_le_iff₀ hN_real_pos]
      have ht_one : t = 1 := le_antisymm ht.2 h_ge
      rw [ht_one]
      have : ((N - 1 : ℕ) : ℝ) ≤ N := by
        push_cast
        have hN_cast : (1 : ℝ) ≤ N := by exact_mod_cast hN
        have h1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          push_cast
          rw [Nat.cast_sub hN]
          push_cast; ring
        rw [h1]; linarith
      linarith
    · push_cast
      have h_div_eq : ((N - 1 : ℕ) : ℝ) + 1 = N := by
        have h1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub hN]
          push_cast; ring
        rw [h1]; ring
      rw [h_div_eq, div_self (ne_of_gt hN_real_pos)]
      exact ht.2
  · -- Case: 0 < t, t < 1. Then whichPiece = min ⌊tN⌋₊ (N-1).
    push_neg at h_le h_ge
    have h_tN_nn : 0 ≤ t * N := by positivity
    have h_tN_lt_N : t * N < N := by nlinarith
    have h_floor_lt_N : ⌊t * N⌋₊ < N := by
      have h1 : (⌊t * N⌋₊ : ℝ) ≤ t * N := Nat.floor_le h_tN_nn
      have h2 : (⌊t * N⌋₊ : ℝ) < N := lt_of_le_of_lt h1 h_tN_lt_N
      exact_mod_cast h2
    have h_floor_le_Nm1 : ⌊t * N⌋₊ ≤ N - 1 := by omega
    have h_min_eq : min (⌊t * N⌋₊) (N - 1) = ⌊t * N⌋₊ := min_eq_left h_floor_le_Nm1
    rw [h_min_eq]
    constructor
    · -- ⌊tN⌋₊ / N ≤ t.
      push_cast
      rw [div_le_iff₀ hN_real_pos]
      exact Nat.floor_le h_tN_nn
    · -- t ≤ (⌊tN⌋₊ + 1) / N.
      push_cast
      rw [le_div_iff₀ hN_real_pos]
      have h := Nat.lt_floor_add_one (t * N)
      linarith

/-! ## `mkQ ∘ pwLiftGlobal = γ.ambient` on `Icc 0 1` -/

/-- **Lift identity on `Icc 0 1`**: `mkQ ∘ pwLiftGlobal = γ.ambient`
on `[0, 1]`, under the chart-anchor partition hypothesis. -/
theorem mkQ_pwLiftGlobal_on_Icc01
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    L.mkQ (pwLiftGlobal L xs γ N t) = γ.ambient t := by
  unfold pwLiftGlobal
  have hk_lt : whichPiece N t < N := whichPiece_lt_of_Icc01 N hN t ht
  obtain ⟨h_t_lower, h_t_upper⟩ := t_in_whichPiece_subInterval N hN t ht
  exact mkQ_pwLiftPiece L xs γ N hN (whichPiece N t) hk_lt h_partition h_src t
    ⟨h_t_lower, h_t_upper⟩

end ComplexTorus

end JacobianChallenge

end
