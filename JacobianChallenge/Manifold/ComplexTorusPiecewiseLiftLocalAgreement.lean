/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusPiecewiseLiftSeam
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Local agreement of consecutive per-piece lifts in a seam neighborhood

The substantive lemma for global smoothness across seams: on a small
open interval around the seam point `t₀ := (k+1)/N`, the two consecutive
per-piece lifts `pwLiftPiece k` and `pwLiftPiece (k+1)` are *equal as
functions of `t`*, not merely equal at the seam point.

Argument:

* Let `Δ(t) := pwLiftPiece k t - pwLiftPiece (k+1) t = (chart_{xs k}).symm
  (γ.ambient t) - (chart_{xs (k+1)}).symm (γ.ambient t) + (shift k - shift (k+1))`.
* `Δ` is continuous on the open intersection
  `γ.ambient ⁻¹ (chart_k.symm.source) ∩ γ.ambient ⁻¹ (chart_{k+1}.symm.source)`.
* For every `t` in the intersection,
  `(chart_{xs k}).symm (γ.ambient t) - (chart_{xs (k+1)}).symm (γ.ambient t) ∈ L`
  by `chart_symm_diff_mem_L`. Since `shift k, shift (k+1) ∈ L`, `Δ(t) ∈ L`.
* At the seam, `Δ(t₀) = 0` by `pwLiftPiece_seam_consistency`.
* By `discRadius_separates`, any `v ∈ L` with `‖v‖ < discRadius L` is `0`.
* By continuity of `Δ` at `t₀`, there is `ε > 0` with `‖Δ(t)‖ < discRadius L`
  for `t` in `Ioo (t₀ - ε) (t₀ + ε)`. Combined with `Δ(t) ∈ L`, `Δ(t) = 0`.

This local agreement is the missing piece to glue the per-piece lifts
into a single C^∞ function on a neighborhood of every seam — hence
globally on `Icc 0 1`.

## What this file ships

* `ComplexTorus.pwLiftPiece_eqOn_seam_nbhd` — there exists a small
  open interval around the seam on which the two consecutive per-piece
  lifts are equal.

No `sorry`, no `axiom`. -/

open Set Metric Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Continuity of the per-piece difference on the chart-overlap -/

private lemma chartSymm_comp_ambient_continuousOn
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (x : ℂ) :
    ContinuousOn
      (fun t : ℝ => (localChart L (discRadius_separates L) x).symm (γ.ambient t))
      (γ.ambient ⁻¹' (localChart L (discRadius_separates L) x).symm.source) := by
  -- Chart-symm-of-γ.ambient: γ.ambient continuous, chart-symm continuous on its source.
  have h_amb : Continuous γ.ambient := γ.ambient_contMDiff.continuous
  have h_chart : ContinuousOn
      (localChart L (discRadius_separates L) x).symm
      (localChart L (discRadius_separates L) x).symm.source :=
    (localChart L (discRadius_separates L) x).symm.continuousOn
  -- Compose: chart_symm continuous-on its source, composed with continuous γ.ambient.
  exact h_chart.comp h_amb.continuousOn (fun _ ht => ht)

/-! ## Discrete-separation: small `L`-valued vectors are zero -/

private lemma L_mem_norm_lt_discRadius_eq_zero {v : ℂ}
    (hv_mem : v ∈ L) (hv_norm : ‖v‖ < discRadius L) :
    v = 0 := by
  exact discRadius_separates L v hv_mem hv_norm

/-! ## Local agreement of `pwLiftPiece k` and `pwLiftPiece (k+1)`
near the seam -/

/-- **Local agreement.** On a small open interval around the seam
point `(k+1)/N`, the two consecutive per-piece lifts are equal. -/
theorem pwLiftPiece_eqOn_seam_nbhd
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : k + 1 < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ∃ ε > 0, ∀ t : ℝ, t ∈ Set.Ioo (((k : ℝ) + 1) / N - ε) (((k : ℝ) + 1) / N + ε) →
      pwLiftPiece L xs γ N k t = pwLiftPiece L xs γ N (k + 1) t := by
  -- Set up the difference function and its key properties.
  set t₀ : ℝ := ((k : ℝ) + 1) / N with ht₀_def
  set Δ : ℝ → ℂ := fun t =>
    pwLiftPiece L xs γ N k t - pwLiftPiece L xs γ N (k + 1) t with hΔ_def
  -- (a) Δ(t₀) = 0 by seam consistency.
  have hΔ_zero : Δ t₀ = 0 := by
    show pwLiftPiece L xs γ N k t₀ - pwLiftPiece L xs γ N (k + 1) t₀ = 0
    rw [pwLiftPiece_seam_consistency L xs γ N k]
    ring
  -- (b) The seam point is in both chart-source preimages.
  have h_kp1_lt_N : k + 1 < N := hk
  have h_k_lt_N : k < N := Nat.lt_of_succ_lt hk
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
  have h_t₀_in_k : γ.ambient t₀ ∈
      (localChart L (discRadius_separates L) (xs k)).symm.source := by
    apply h_partition k h_k_lt_N t₀
    · rw [ht₀_def]; apply div_le_div_of_nonneg_right _ hN_real_pos.le; linarith
    · exact le_refl _
  have h_t₀_in_kp1 : γ.ambient t₀ ∈
      (localChart L (discRadius_separates L) (xs (k+1))).symm.source := by
    apply h_partition (k+1) h_kp1_lt_N t₀
    · rw [ht₀_def]; push_cast; linarith
    · rw [ht₀_def]; apply div_le_div_of_nonneg_right _ hN_real_pos.le; push_cast; linarith
  -- (c) Open intersection.
  set U : Set ℝ :=
    γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs k)).symm.source ∩
      γ.ambient ⁻¹' (localChart L (discRadius_separates L) (xs (k+1))).symm.source
    with hU_def
  have h_amb_cont : Continuous γ.ambient := γ.ambient_contMDiff.continuous
  have hU_open : IsOpen U :=
    ((localChart L (discRadius_separates L) (xs k)).symm.open_source.preimage h_amb_cont).inter
      ((localChart L (discRadius_separates L) (xs (k+1))).symm.open_source.preimage h_amb_cont)
  have h_t₀_in_U : t₀ ∈ U := ⟨h_t₀_in_k, h_t₀_in_kp1⟩
  -- (d) Δ is continuous on U.
  have hΔ_cont : ContinuousOn Δ U := by
    have h1 : ContinuousOn
        (fun t : ℝ => (localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t)) U :=
      (chartSymm_comp_ambient_continuousOn L γ (xs k)).mono (fun _ ht => ht.1)
    have h2 : ContinuousOn
        (fun t : ℝ => (localChart L (discRadius_separates L) (xs (k+1))).symm
            (γ.ambient t)) U :=
      (chartSymm_comp_ambient_continuousOn L γ (xs (k+1))).mono (fun _ ht => ht.2)
    have h3 : ContinuousOn (fun _ : ℝ => cumulativeShift L xs γ N k) U :=
      continuousOn_const
    have h4 : ContinuousOn (fun _ : ℝ => cumulativeShift L xs γ N (k+1)) U :=
      continuousOn_const
    -- Δ = (chart_k(γ.ambient) + shift k) - (chart_{k+1}(γ.ambient) + shift (k+1)).
    have h_eq : Δ = fun t =>
        ((localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t)
          + cumulativeShift L xs γ N k)
        - ((localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient t)
          + cumulativeShift L xs γ N (k+1)) := by
      funext t; rfl
    rw [h_eq]
    exact (h1.add h3).sub (h2.add h4)
  -- (e) Δ(t) ∈ L for t ∈ U.
  have h_shift_k_in_L : cumulativeShift L xs γ N k ∈ L :=
    cumulativeShift_mem_L L γ h_src N hN xs h_partition k h_k_lt_N
  have h_shift_kp1_in_L : cumulativeShift L xs γ N (k+1) ∈ L :=
    cumulativeShift_mem_L L γ h_src N hN xs h_partition (k+1) hk
  have hΔ_in_L : ∀ t ∈ U, Δ t ∈ L := by
    intro t ⟨ht_k, ht_kp1⟩
    -- Δ t = chart_k(γ.ambient t) + shift k - (chart_{k+1}(γ.ambient t) + shift (k+1))
    --     = (chart_k(γ.ambient t) - chart_{k+1}(γ.ambient t)) + (shift k - shift (k+1)).
    show pwLiftPiece L xs γ N k t - pwLiftPiece L xs γ N (k+1) t ∈ L
    unfold pwLiftPiece
    have h_chart_diff_in_L :
        (localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t) -
          (localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient t) ∈ L :=
      chart_symm_diff_mem_L L (xs k) (xs (k+1)) ht_k ht_kp1
    have h_shift_diff_in_L : cumulativeShift L xs γ N k - cumulativeShift L xs γ N (k+1) ∈ L :=
      Submodule.sub_mem L h_shift_k_in_L h_shift_kp1_in_L
    have h_eq :
        (localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t)
          + cumulativeShift L xs γ N k
        - ((localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient t)
          + cumulativeShift L xs γ N (k+1))
        = ((localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t) -
            (localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient t))
          + (cumulativeShift L xs γ N k - cumulativeShift L xs γ N (k+1)) := by ring
    rw [h_eq]
    exact Submodule.add_mem L h_chart_diff_in_L h_shift_diff_in_L
  -- (f) Pick ε such that Ioo (t₀ - ε) (t₀ + ε) ⊆ U and ‖Δ t‖ < discRadius L on this Ioo.
  have hr_pos : (0 : ℝ) < discRadius L := discRadius_pos L
  -- U is open, contains t₀. So there's δ_U > 0 with ball t₀ δ_U ⊆ U.
  rcases Metric.isOpen_iff.mp hU_open t₀ h_t₀_in_U with ⟨δ_U, hδ_U_pos, hδ_U_sub⟩
  -- Δ is continuous at t₀ (via ContinuousOn). Find δ_norm > 0 with dist (Δ t) (Δ t₀) < discRadius L
  -- for t ∈ ball t₀ δ_norm ∩ U. Since Δ t₀ = 0, ‖Δ t‖ < discRadius L.
  have hΔ_cont_t₀ : ContinuousWithinAt Δ U t₀ := hΔ_cont t₀ h_t₀_in_U
  obtain ⟨δ_norm, hδ_norm_pos, hδ_norm_dist⟩ :=
    Metric.continuousWithinAt_iff.mp hΔ_cont_t₀ (discRadius L) hr_pos
  -- hδ_norm_dist : ∀ x ∈ U, dist x t₀ < δ_norm → dist (Δ x) (Δ t₀) < discRadius L.
  have hδ_norm_lt : ∀ t ∈ Metric.ball t₀ δ_norm, t ∈ U → ‖Δ t‖ < discRadius L := by
    intro t ht_ball ht_U
    have h_dist : dist t t₀ < δ_norm := by
      rw [Metric.mem_ball] at ht_ball; exact ht_ball
    have h := hδ_norm_dist ht_U h_dist
    rw [hΔ_zero, dist_zero_right] at h
    exact h
  -- (g) Pick ε := min δ_U δ_norm > 0.
  let ε : ℝ := min δ_U δ_norm
  have hε_pos : 0 < ε := lt_min hδ_U_pos hδ_norm_pos
  refine ⟨ε, hε_pos, ?_⟩
  intro t ht_in_Ioo
  -- t ∈ Ioo (t₀-ε) (t₀+ε) ⊆ ball t₀ ε ⊆ U ∩ ball t₀ δ_norm.
  have h_in_ball_ε : t ∈ Metric.ball t₀ ε := by
    rw [Metric.mem_ball, dist_comm, Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith [ht_in_Ioo.1, ht_in_Ioo.2]
  have h_in_U : t ∈ U := hδ_U_sub (by
    have := h_in_ball_ε
    apply Metric.ball_subset_ball (min_le_left _ _) this)
  have h_in_ball_norm : t ∈ Metric.ball t₀ δ_norm :=
    Metric.ball_subset_ball (min_le_right _ _) h_in_ball_ε
  have h_norm_lt : ‖Δ t‖ < discRadius L := hδ_norm_lt t h_in_ball_norm h_in_U
  -- Δ t ∈ L and ‖Δ t‖ < discRadius L → Δ t = 0 → pwLiftPiece equality.
  have hΔ_t_in_L : Δ t ∈ L := hΔ_in_L t h_in_U
  have hΔ_t_zero : Δ t = 0 := L_mem_norm_lt_discRadius_eq_zero L hΔ_t_in_L h_norm_lt
  -- Δ t = 0 → pwLiftPiece k t = pwLiftPiece (k+1) t.
  have h_eq_zero : pwLiftPiece L xs γ N k t - pwLiftPiece L xs γ N (k+1) t = 0 := hΔ_t_zero
  linear_combination h_eq_zero

end ComplexTorus

end JacobianChallenge

end
