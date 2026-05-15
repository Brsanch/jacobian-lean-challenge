/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2LoopLebesgueSubdivision
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Chart-indexed equidistant partition of an `S²`-valued loop

Refines `exists_lebesgue_radius_for_two_chart_cover`
(`Topology/S2LoopLebesgueSubdivision.lean`) into an explicit
equidistant partition of `unitInterval` indexed by a chart choice per
sub-interval.

For any continuous `f : C(unitInterval, sphere 0 1)` and unit vector
`v`, the Lebesgue lemma gives `δ > 0` such that every `δ`-ball in
`unitInterval` maps into one of the two stereographic chart sources.
Pick `N : ℕ` with `1/N < δ`. Partition `unitInterval` into
`[k/N, (k+1)/N]` for `k = 0, …, N-1`. Each sub-interval has length
`1/N < δ`, hence lies inside the open `δ`-ball around its midpoint,
hence `f` maps it into a single chart's source. Record the choice
of chart per sub-interval as a function `chart : Fin N → Set …`.

This packages the discrete data the upcoming polygonal-approximation
homotopy needs: the partition vertices `0 = t₀ < t₁ < … < t_N = 1`
and the chart `Uᵢ ∋ f(t_i), …, f(t_{i+1})` containing each sub-image.

## What is proved

* `JacobianChallenge.exists_chart_indexed_partition` — for every
  continuous `f : C(unitInterval, sphere 0 1)` and unit vector
  `v ∈ EuclideanSpace ℝ (Fin 3)`, there is `N : ℕ` with `0 < N` and a
  chart-assignment `chart : Fin N → Set (sphere 0 1)` (each value is
  one of the two stereographic chart sources), such that every
  `s : unitInterval` with `(k:ℝ)/N ≤ (s:ℝ) ≤ ((k:ℝ)+1)/N` has
  `f s ∈ chart k`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)}

/-- **Chart-indexed equidistant partition.** Given a continuous loop
parameter `f : C(unitInterval, sphere 0 1)` and a unit vector `v`, this
produces a positive integer `N`, a per-sub-interval choice of
stereographic chart (north or south), and a guarantee that the image
of each equidistant sub-interval `[k/N, (k+1)/N]` under `f` lies in
the chosen chart's source.

The proof:

1. Get the Lebesgue radius `δ > 0` from
   `exists_lebesgue_radius_for_two_chart_cover`.
2. Pick `N : ℕ` with `1/N < δ` using `exists_nat_gt (1/δ)`. We make
   sure to take `max N 1` so positivity is automatic.
3. For each `k : Fin N`, set the midpoint
   `c_k := (2k+1)/(2N) ∈ unitInterval`; the Lebesgue lemma applied at
   `c_k` produces one of the two chart sources; record it as `chart k`.
4. The sub-interval `[k/N, (k+1)/N]` lies in `Metric.ball c_k δ`
   because every point in it is within distance `1/(2N) < δ/2 < δ`
   of `c_k`. The Lebesgue lemma then transports the containment to
   `chart k`. -/
theorem exists_chart_indexed_partition
    (f : C(unitInterval, sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) (hv : ‖v‖ = 1) :
    ∃ (N : ℕ), 0 < N ∧
      ∃ chart : Fin N → Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        (∀ k, chart k = (stereographic hv).source ∨
              chart k = (stereographic (norm_neg_one_of_norm_one hv)).source) ∧
        ∀ (k : Fin N) (s : unitInterval),
          ((k : ℝ) / N) ≤ (s : ℝ) → (s : ℝ) ≤ ((k : ℝ) + 1) / N →
          f s ∈ chart k := by
  -- Step 1: Lebesgue radius δ > 0 from chip 4b.
  obtain ⟨δ, hδ_pos, hball⟩ := exists_lebesgue_radius_for_two_chart_cover hv f
  -- Step 2: pick N : ℕ with 1/N < δ (and N ≥ 1 for positivity).
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  let N : ℕ := max M 1
  have hN_pos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hN_cast_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos
  -- Establish 1/N < δ. From hM : 1/δ < M and 1/δ > 0, deduce M > 0,
  -- hence M ≥ 1, hence 1 < M * δ, hence 1/M < δ, hence 1/N ≤ 1/M < δ.
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
  -- Helper: produce the midpoint of [k/N, (k+1)/N] inside unitInterval.
  have hk_div_le : ∀ k : Fin N, ((k : ℝ) + 1) / N ≤ 1 := by
    intro k
    rw [div_le_one hN_cast_pos]
    have : (k : ℕ) + 1 ≤ N := k.isLt
    exact_mod_cast this
  have hk_div_nn : ∀ k : Fin N, 0 ≤ (k : ℝ) / N := by
    intro k
    positivity
  -- For each k, define midpoint c_k = (2k+1)/(2N) and apply the Lebesgue lemma.
  set ck : Fin N → unitInterval := fun k =>
    ⟨((2 * (k : ℝ) + 1) / (2 * N)),
      by
        constructor
        · positivity
        · rw [div_le_one (by positivity)]
          have hk : (k : ℕ) + 1 ≤ N := k.isLt
          have : (2 * (k : ℝ) + 1) ≤ 2 * N := by
            have : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
            linarith
          linarith⟩ with hck_def
  -- For each k, choose the chart via the Lebesgue lemma at ck k.
  classical
  let chart : Fin N → Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := fun k =>
    if Metric.ball (ck k) δ ⊆ f ⁻¹' (stereographic hv).source then
      (stereographic hv).source
    else
      (stereographic (norm_neg_one_of_norm_one hv)).source
  refine ⟨N, hN_pos, chart, ?_, ?_⟩
  · -- Each chart k is one of the two named sources.
    intro k
    simp only [chart]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · -- Membership: every s ∈ [k/N, (k+1)/N] has f s ∈ chart k.
    intro k s hs_lower hs_upper
    -- Show s is in Metric.ball (ck k) δ.
    have h_dist : dist s (ck k) < δ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      have h_mid : (ck k : ℝ) = (2 * (k : ℝ) + 1) / (2 * N) := rfl
      have h_two_N : (0 : ℝ) < 2 * N := by positivity
      have h_lhs : (s : ℝ) - (ck k : ℝ) ≤ 1 / (2 * N) := by
        rw [h_mid]
        have h_k_eq : ((k : ℝ) + 1) / N = (2 * (k : ℝ) + 2) / (2 * N) := by
          field_simp
        rw [h_k_eq] at hs_upper
        have : (s : ℝ) ≤ (2 * (k : ℝ) + 2) / (2 * N) := hs_upper
        have : (s : ℝ) - (2 * (k : ℝ) + 1) / (2 * N) ≤
            (2 * (k : ℝ) + 2) / (2 * N) - (2 * (k : ℝ) + 1) / (2 * N) := by linarith
        have h_diff : (2 * (k : ℝ) + 2) / (2 * N) - (2 * (k : ℝ) + 1) / (2 * N)
            = 1 / (2 * N) := by ring
        linarith
      have h_rhs : (ck k : ℝ) - (s : ℝ) ≤ 1 / (2 * N) := by
        rw [h_mid]
        have h_k_eq : ((k : ℝ)) / N = (2 * (k : ℝ)) / (2 * N) := by field_simp
        rw [h_k_eq] at hs_lower
        have : (2 * (k : ℝ)) / (2 * N) ≤ (s : ℝ) := hs_lower
        have : (2 * (k : ℝ) + 1) / (2 * N) - (s : ℝ) ≤
            (2 * (k : ℝ) + 1) / (2 * N) - (2 * (k : ℝ)) / (2 * N) := by linarith
        have h_diff : (2 * (k : ℝ) + 1) / (2 * N) - (2 * (k : ℝ)) / (2 * N)
            = 1 / (2 * N) := by ring
        linarith
      have h_abs : |(s : ℝ) - (ck k : ℝ)| ≤ 1 / (2 * N) := abs_le.mpr ⟨by linarith, h_lhs⟩
      have h_inv2N_lt : 1 / (2 * N) < δ := by
        have h_half_lt : (1 : ℝ) / (2 * N) ≤ 1 / N := by
          apply div_le_div_of_nonneg_left _ hN_cast_pos
          · linarith
          · norm_num
        linarith
      linarith
    -- Apply the Lebesgue lemma at ck k.
    have h_choice := hball (ck k)
    -- Case-split via the `if` defining `chart k`.
    show f s ∈ chart k
    simp only [chart]
    rcases h_choice with h_north | h_south
    · -- North chart contains the δ-ball around ck k.
      rw [if_pos h_north]
      have h_s_in_ball : s ∈ Metric.ball (ck k) δ := by
        rw [Metric.mem_ball]; exact h_dist
      exact h_north h_s_in_ball
    · -- South chart contains it.
      by_cases h_n : Metric.ball (ck k) δ ⊆ f ⁻¹' (stereographic hv).source
      · rw [if_pos h_n]
        have h_s_in_ball : s ∈ Metric.ball (ck k) δ := by
          rw [Metric.mem_ball]; exact h_dist
        exact h_n h_s_in_ball
      · rw [if_neg h_n]
        have h_s_in_ball : s ∈ Metric.ball (ck k) δ := by
          rw [Metric.mem_ball]; exact h_dist
        exact h_south h_s_in_ball

end JacobianChallenge

end
