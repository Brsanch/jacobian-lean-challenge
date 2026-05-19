/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusChartSymmDiff

set_option linter.unusedSectionVars false

/-! # Cumulative seam-shift for piecewise smooth lifts on `ℂ ⧸ L`

For a smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` based at `0`,
together with a chart-anchor partition `xs : ℕ → ℂ` (from
`ComplexTorusLebesgueChartCover`), the cumulative shift defined by
the recursion

  shift 0      := -(chart_{xs 0}).symm (γ.ambient 0)
  shift (k+1)  := shift k + (chart_{xs k}).symm (γ.ambient ((k+1)/N))
                          - (chart_{xs (k+1)}).symm (γ.ambient ((k+1)/N))

is the value that, when added pointwise to the per-piece chart-symm
composition `(chart_{xs k}).symm ∘ γ.ambient`, yields a piecewise
smooth lift whose pieces agree at the seams.

This file shows that **every cumulative shift `shift k` (for `k < N`)
lies in `L`**, via induction on `k`:

* base `k = 0`: `γ.ambient 0 = γ.src = 0`, so `(chart_{xs 0}).symm 0`
  is in the kernel of `mkQ`, hence in `L`;

* inductive `k → k+1` (requires `k+1 < N`): the increment is
  `(chart_{xs k}).symm q - (chart_{xs (k+1)}).symm q` for
  `q := γ.ambient ((k+1)/N)`, in both chart sources by the partition
  hypothesis at sub-intervals `k` and `k+1`; membership in `L` follows
  from `chart_symm_diff_mem_L`.

## What this file ships

* `ComplexTorus.cumulativeShift` — the recursive shift function.

* `ComplexTorus.ambient_zero` — `γ.ambient 0 = γ.src` (auxiliary).

* `ComplexTorus.cumulativeShift_mem_L` — every shift `shift k` for
  `k < N` lies in `L`, under the chart-anchor partition hypothesis +
  `γ.src = 0`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The cumulative shift, defined recursively on ℕ -/

/-- **Cumulative seam-shift.** Recursive shift function indexed by
`ℕ`. The `Fin N` chart-anchor data is encoded as a (junk-padded)
function `xs : ℕ → ℂ`; the membership-in-`L` theorem below only
constrains `k < N`. -/
noncomputable def cumulativeShift
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) :
    ℕ → ℂ
  | 0 =>
    -((localChart L (discRadius_separates L) (xs 0)).symm (γ.ambient 0))
  | (k + 1) =>
    cumulativeShift xs γ N k
      + (localChart L (discRadius_separates L) (xs k)).symm
          (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))
      - (localChart L (discRadius_separates L) (xs (k + 1))).symm
          (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))

/-! ## Helper: `γ.ambient 0 = γ.src` -/

lemma ambient_zero (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) :
    γ.ambient 0 = γ.src := by
  have h := γ.ambient_eq_on_unitInterval
    (⟨0, by constructor <;> norm_num⟩ : unitInterval)
  have hval : ((⟨0, by constructor <;> norm_num⟩ : unitInterval).val : ℝ) = 0 := rfl
  rw [hval] at h
  rw [h]
  exact γ.toPath.source

/-! ## `cumulativeShift_mem_L` -/

/-- **Cumulative shifts lie in `L`.** Under `γ.src = 0`, `0 < N`, and
the chart-anchor partition hypothesis on indices `0, …, N - 1`, every
cumulative shift `shift k` (for `k < N`) is in the lattice `L`. -/
theorem cumulativeShift_mem_L
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (h_src : γ.src = (0 : ℂ ⧸ L))
    (N : ℕ) (hN : 0 < N) (xs : ℕ → ℂ)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ∀ k : ℕ, k < N → cumulativeShift L xs γ N k ∈ L := by
  intro k hk
  induction k with
  | zero =>
    -- Base: shift 0 = -(chart_{xs 0}).symm (γ.ambient 0).
    show cumulativeShift L xs γ N 0 ∈ L
    rw [show cumulativeShift L xs γ N 0
        = -((localChart L (discRadius_separates L) (xs 0)).symm (γ.ambient 0))
        from rfl]
    refine Submodule.neg_mem L ?_
    -- γ.ambient 0 ∈ chart source via h_partition at k=0, s=0.
    have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
    have h_0_lower : ((0 : ℕ) : ℝ) / N ≤ (0 : ℝ) := by push_cast; simp
    have h_0_upper : (0 : ℝ) ≤ (((0 : ℕ) : ℝ) + 1) / N := by push_cast; positivity
    have h_in : γ.ambient (0 : ℝ) ∈
        (localChart L (discRadius_separates L) (xs 0)).symm.source :=
      h_partition 0 hN 0 h_0_lower h_0_upper
    -- mkQ ((chart).symm (γ.ambient 0)) = γ.ambient 0 = γ.src = 0.
    have h_mkQ : L.mkQ ((localChart L (discRadius_separates L) (xs 0)).symm
        (γ.ambient 0)) = γ.ambient 0 := mkQ_chart_symm L (xs 0) h_in
    have h_amb_zero : γ.ambient 0 = (0 : ℂ ⧸ L) := by
      rw [ambient_zero L γ, h_src]
    rw [h_amb_zero] at h_mkQ
    -- h_mkQ : L.mkQ ((chart).symm 0) = 0. Want ((chart).symm 0) ∈ L.
    -- After h_amb_zero rewrite, the goal is `(chart).symm 0 ∈ L`.
    -- But the goal still mentions γ.ambient 0 via the original neg_mem. Rewrite first.
    rw [h_amb_zero]
    exact (Submodule.Quotient.mk_eq_zero L).mp h_mkQ
  | succ k ih =>
    -- Inductive: shift (k+1) = shift k + Δ, with Δ ∈ L by chart_symm_diff_mem_L.
    have hk_lt_N : k < N := Nat.lt_of_succ_lt hk
    have ih_in_L := ih hk_lt_N
    have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN
    -- The seam point s := (k+1)/N.
    set s : ℝ := ((k : ℝ) + 1) / (N : ℝ) with hs_def
    -- Apply h_partition at index k.
    have h_s_ge_k : (k : ℝ) / N ≤ s := by
      rw [hs_def]
      apply div_le_div_of_nonneg_right _ hN_real_pos.le
      linarith
    have h_s_le_kp1 : s ≤ ((k : ℝ) + 1) / N := le_of_eq hs_def
    have h_q_in_k : γ.ambient s ∈
        (localChart L (discRadius_separates L) (xs k)).symm.source :=
      h_partition k hk_lt_N s h_s_ge_k h_s_le_kp1
    -- Apply h_partition at index (k+1). (k+1) < N from hk : k + 1 < N.
    have h_kp1_lt : k + 1 < N := hk
    have h_s_ge_kp1_idx : (((k + 1 : ℕ) : ℝ)) / N ≤ s := by
      rw [hs_def]
      push_cast
      linarith
    have h_s_le_kp2 : s ≤ (((k + 1 : ℕ) : ℝ) + 1) / N := by
      rw [hs_def]
      apply div_le_div_of_nonneg_right _ hN_real_pos.le
      push_cast
      linarith
    have h_q_in_kp1 : γ.ambient s ∈
        (localChart L (discRadius_separates L) (xs (k + 1))).symm.source :=
      h_partition (k + 1) h_kp1_lt s h_s_ge_kp1_idx h_s_le_kp2
    -- Δ := (chart_{xs k}).symm (γ.ambient s) - (chart_{xs (k+1)}).symm (γ.ambient s) ∈ L.
    have h_diff_in_L :
        (localChart L (discRadius_separates L) (xs k)).symm (γ.ambient s)
          - (localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient s) ∈ L :=
      chart_symm_diff_mem_L L (xs k) (xs (k+1)) h_q_in_k h_q_in_kp1
    -- shift (k+1) = shift k + Δ ∈ L.
    show cumulativeShift L xs γ N (k+1) ∈ L
    have h_rec : cumulativeShift L xs γ N (k+1)
        = cumulativeShift L xs γ N k
          + ((localChart L (discRadius_separates L) (xs k)).symm
              (γ.ambient s)
            - (localChart L (discRadius_separates L) (xs (k+1))).symm
                (γ.ambient s)) := by
      show cumulativeShift L xs γ N k
          + (localChart L (discRadius_separates L) (xs k)).symm
              (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))
          - (localChart L (discRadius_separates L) (xs (k + 1))).symm
              (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))
        = cumulativeShift L xs γ N k
          + ((localChart L (discRadius_separates L) (xs k)).symm (γ.ambient s)
            - (localChart L (discRadius_separates L) (xs (k+1))).symm (γ.ambient s))
      rw [hs_def]
      ring
    rw [h_rec]
    exact Submodule.add_mem L ih_in_L h_diff_in_L

end ComplexTorus

end JacobianChallenge

end
