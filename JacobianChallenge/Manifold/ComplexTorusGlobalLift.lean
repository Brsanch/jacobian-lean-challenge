/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusPiecewiseLiftLocalAgreement

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Global piecewise lift on `ℝ` for `ℂ ⧸ L`

Glues the per-piece smooth lifts `pwLiftPiece L xs γ N k` together
into a single function `ℝ → ℂ` via a piece-selector `whichPiece`.

The piece index for a parameter `t : ℝ` is `whichPiece N t`, clipped
to `[0, N - 1]`. On the strict sub-intervals `[k/N, (k+1)/N)`,
`whichPiece N t = k`. At seam points `t = (k+1)/N`, the values
`pwLiftPiece L xs γ N k t` and `pwLiftPiece L xs γ N (k+1) t`
coincide (by `pwLiftPiece_seam_consistency`).

## What this file ships

* `ComplexTorus.whichPiece` — the piece-index function.

* `ComplexTorus.pwLiftGlobal` — the global piecewise lift function
  `ℝ → ℂ`.

* `ComplexTorus.whichPiece_lt_of_Icc01` — for `t ∈ Icc 0 1`,
  `whichPiece N t < N`.

* `ComplexTorus.pwLiftGlobal_at_zero` — `pwLiftGlobal _ _ _ _ 0 = 0`.

The lift identity `mkQ ∘ pwLiftGlobal = γ.ambient` on `Icc 0 1` and the
global smoothness are landed in follow-up chips.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## The piece-index function -/

/-- **Piece index.** For `t : ℝ` and `N : ℕ`, returns `⌊t · N⌋₊` clipped
to `[0, N - 1]`. -/
noncomputable def whichPiece (N : ℕ) (t : ℝ) : ℕ :=
  if t ≤ 0 then 0
  else if 1 ≤ t then N - 1
  else min (⌊t * N⌋₊) (N - 1)

/-! ## The global piecewise lift -/

/-- **Global piecewise lift.** Selects the per-piece lift based on
`whichPiece`. -/
noncomputable def pwLiftGlobal
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) (t : ℝ) : ℂ :=
  pwLiftPiece L xs γ N (whichPiece N t) t

/-! ## `whichPiece` bound on `Icc 0 1` -/

/-- For `t ∈ Icc 0 1`, `whichPiece N t < N`. -/
theorem whichPiece_lt_of_Icc01
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    whichPiece N t < N := by
  unfold whichPiece
  split_ifs with h_le h_ge
  · exact hN
  · omega
  · exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)

/-! ## Value at zero -/

/-- **`pwLiftGlobal _ _ _ _ 0 = 0`** under the standard hypotheses
(implicit in `pwLiftPiece_zero_at_zero'`). -/
theorem pwLiftGlobal_at_zero
    (xs : ℕ → ℂ) (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L)) (N : ℕ) :
    pwLiftGlobal L xs γ N 0 = 0 := by
  unfold pwLiftGlobal whichPiece
  simp
  exact pwLiftPiece_zero_at_zero' L xs γ N

end ComplexTorus

end JacobianChallenge

end
