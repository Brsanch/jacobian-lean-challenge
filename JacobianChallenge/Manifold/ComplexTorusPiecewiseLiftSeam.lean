/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusPiecewiseLift

set_option linter.unusedSectionVars false

/-! # Seam consistency for the per-piece smooth lift on `ℂ ⧸ L`

The cumulative seam-shift `cumulativeShift L xs γ N` is chosen
exactly so that the per-piece lifts `pwLiftPiece k` and
`pwLiftPiece (k+1)` agree at the shared seam point `t = (k+1)/N`.

This identity is a pure algebraic consequence of the recursion
defining `cumulativeShift`:

  shift (k+1) = shift k + chart_k_value - chart_{k+1}_value

at the seam, where `chart_i_value := (chart_{xs i}).symm (γ.ambient((k+1)/N))`.
Then:

  pwLiftPiece k     seam = chart_k_value + shift k
  pwLiftPiece (k+1) seam = chart_{k+1}_value + shift (k+1)
                         = chart_{k+1}_value + shift k + chart_k_value - chart_{k+1}_value
                         = chart_k_value + shift k
                         = pwLiftPiece k seam.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Seam consistency**: the per-piece lifts agree at the shared
seam `t = (k+1)/N`. -/
theorem pwLiftPiece_seam_consistency
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) (k : ℕ) :
    pwLiftPiece L xs γ N k (((k : ℝ) + 1) / N) =
      pwLiftPiece L xs γ N (k + 1) (((k : ℝ) + 1) / N) := by
  -- Unfold both sides and use the recursion of cumulativeShift.
  unfold pwLiftPiece
  -- cumulativeShift (k+1) := cumulativeShift k + chart_k_value - chart_{k+1}_value.
  -- chart_i_value here := (chart_{xs i}).symm (γ.ambient ((k+1)/N)).
  -- The recursion gives precisely the algebraic match.
  show (localChart L (discRadius_separates L) (xs k)).symm
        (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))
      + cumulativeShift L xs γ N k
    = (localChart L (discRadius_separates L) (xs (k + 1))).symm
        (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))
      + cumulativeShift L xs γ N (k + 1)
  rw [show cumulativeShift L xs γ N (k + 1)
      = cumulativeShift L xs γ N k
        + (localChart L (discRadius_separates L) (xs k)).symm
            (γ.ambient (((k : ℝ) + 1) / (N : ℝ)))
        - (localChart L (discRadius_separates L) (xs (k + 1))).symm
            (γ.ambient (((k : ℝ) + 1) / (N : ℝ))) from rfl]
  ring

end ComplexTorus

end JacobianChallenge

end
