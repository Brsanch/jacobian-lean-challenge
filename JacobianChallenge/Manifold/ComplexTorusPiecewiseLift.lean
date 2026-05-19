/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusChartLiftOnSubinterval
import JacobianChallenge.Manifold.ComplexTorusCumulativeShift

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Per-piece smooth lift on `ℂ ⧸ L` via chart-symm + cumulative shift

For a smooth path `γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)` based at `0`,
chart-anchor partition `(N, xs)`, and cumulative shift function
`cumulativeShift L xs γ N`, the per-piece function

  `pwLiftPiece k t := (chart_{xs k}).symm (γ.ambient t)
                       + cumulativeShift L xs γ N k`

is a smooth ℂ-valued lift of `γ.ambient` on the sub-interval
`Icc (k/N) ((k+1)/N)`:

* `ContMDiffOn` at level `∞` (chart-symm composition is smooth +
  adding a constant preserves smoothness);

* `mkQ (pwLiftPiece k t) = γ.ambient t` on the sub-interval (since
  the cumulative shift lies in `L` and `mkQ` ignores `L`).

The piece-0 boundary value is `0`: `pwLiftPiece 0 0 = 0`, by the
defining recursion of `cumulativeShift 0`.

This is the per-piece data the global piecewise lift glues together
via the seam-consistency identity from the next chip.

## What this file ships

* `ComplexTorus.pwLiftPiece` — the per-piece smooth lift.

* `ComplexTorus.pwLiftPiece_contMDiffOn` — smoothness on
  `Icc (k/N) ((k+1)/N)`.

* `ComplexTorus.mkQ_pwLiftPiece` — `mkQ ∘ pwLiftPiece k = γ.ambient`
  on the sub-interval.

* `ComplexTorus.pwLiftPiece_zero_at_zero` — `pwLiftPiece 0 0 = 0`,
  under the standard hypotheses.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Per-piece smooth lift -/

/-- **Per-piece smooth lift.** The chart-symm composition shifted by
the cumulative seam-shift; equals a smooth ℂ-valued lift of `γ.ambient`
on the `k`-th sub-interval. -/
noncomputable def pwLiftPiece
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) (k : ℕ) (t : ℝ) : ℂ :=
  (localChart L (discRadius_separates L) (xs k)).symm (γ.ambient t)
    + cumulativeShift L xs γ N k

/-! ## Per-piece smoothness -/

/-- **The per-piece lift is `ContMDiffOn` on the sub-interval.** -/
theorem pwLiftPiece_contMDiffOn
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) (hN : 0 < N) (k : ℕ)
    (hk : k < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (pwLiftPiece L xs γ N k)
      (Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) := by
  -- pwLiftPiece k t = chartLift_k t + const(shift k). ContMDiffOn under .add_const.
  have h_chart_smooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun t : ℝ => (localChart L (discRadius_separates L) (xs k)).symm
          (γ.ambient t))
      (Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) := by
    refine chartLift_contMDiffOn_subinterval L γ (xs k) ?_
    intro t ht
    exact h_partition k hk t ht.1 ht.2
  -- Adding a constant preserves ContMDiffOn.
  unfold pwLiftPiece
  exact h_chart_smooth.add contMDiffOn_const

/-! ## `mkQ ∘ pwLiftPiece = γ.ambient` -/

/-- **`mkQ ∘ pwLiftPiece k = γ.ambient`** on the `k`-th sub-interval. -/
theorem mkQ_pwLiftPiece
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) (hN : 0 < N) (k : ℕ)
    (hk : k < N)
    (h_partition : ∀ k : ℕ, k < N → ∀ s : ℝ,
        (k : ℝ) / N ≤ s → s ≤ ((k : ℝ) + 1) / N →
        γ.ambient s ∈ (localChart L (discRadius_separates L) (xs k)).symm.source)
    (h_src : γ.src = (0 : ℂ ⧸ L))
    (t : ℝ) (ht : t ∈ Set.Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :
    L.mkQ (pwLiftPiece L xs γ N k t) = γ.ambient t := by
  unfold pwLiftPiece
  -- mkQ (chart_symm + shift) = mkQ chart_symm + mkQ shift = γ.ambient t + 0
  -- (since shift k ∈ L, mkQ shift = 0).
  rw [map_add]
  -- mkQ ((chart).symm (γ.ambient t)) = γ.ambient t via mkQ_chart_symm.
  have h_in : γ.ambient t ∈
      (localChart L (discRadius_separates L) (xs k)).symm.source :=
    h_partition k hk t ht.1 ht.2
  rw [mkQ_chart_symm L (xs k) h_in]
  -- mkQ (shift k) = 0 since shift k ∈ L.
  have h_shift_in_L : cumulativeShift L xs γ N k ∈ L :=
    cumulativeShift_mem_L L γ h_src N hN xs h_partition k hk
  have h_mkQ_shift : L.mkQ (cumulativeShift L xs γ N k) = 0 :=
    (Submodule.Quotient.mk_eq_zero L).mpr h_shift_in_L
  rw [h_mkQ_shift, add_zero]

/-! ## Piece-0 starts at 0 -/

/-- **`pwLiftPiece 0 0 = 0`** under the standard hypotheses. -/
theorem pwLiftPiece_zero_at_zero
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) :
    pwLiftPiece L xs γ N 0 0
      = (localChart L (discRadius_separates L) (xs 0)).symm (γ.ambient 0)
        + (-(localChart L (discRadius_separates L) (xs 0)).symm (γ.ambient 0)) := by
  unfold pwLiftPiece
  -- shift 0 = -(chart_{xs 0}).symm (γ.ambient 0) by definition.
  rfl

/-- **Concise form**: `pwLiftPiece 0 0 = 0`. -/
theorem pwLiftPiece_zero_at_zero'
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) :
    pwLiftPiece L xs γ N 0 0 = 0 := by
  rw [pwLiftPiece_zero_at_zero L xs γ N]
  ring

end ComplexTorus

end JacobianChallenge

end
