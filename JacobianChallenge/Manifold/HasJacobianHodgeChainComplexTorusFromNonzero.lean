/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorusFromOrientation
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorusSwap

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain (ℂ ⧸ L)` from `Im ≠ 0` (chip 19p)

Combines chips 19n (positive orientation) and 19o (negative orientation
via swap) into a single by-cases reduction: `HasJacobianHodgeChain
(ℂ ⧸ L)` holds whenever

  `(star (lam₁_complexTorus L) · (lam₂_complexTorus L)).im ≠ 0`.

The remaining gap to "unconditional" is exactly the structural fact
"ℝ-LI ⟹ Im ≠ 0" for complex pairs (deferred — see comments).

## What this file ships

* `hasJacobianHodgeChain_complexTorus_of_im_ne_zero` — by-cases
  reduction from `Im ≠ 0`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`HasJacobianHodgeChain (ℂ ⧸ L)` from `Im ≠ 0`.** Case-splits on
the sign of `(star lam₁ · lam₂).im`; the positive case uses chip 19n
directly, the negative case applies the swap chip 19o. -/
theorem hasJacobianHodgeChain_complexTorus_of_im_ne_zero
    (h_orient_ne :
        (star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im ≠ 0) :
    HasJacobianHodgeChain (ℂ ⧸ L) := by
  rcases lt_or_gt_of_ne h_orient_ne with h_neg | h_pos
  · -- Negative case: swap.
    exact hasJacobianHodgeChain_complexTorus_of_orientation_neg L h_neg
  · -- Positive case: use directly.
    exact hasJacobianHodgeChain_complexTorus_of_orientation L h_pos

end ComplexTorus

end JacobianChallenge

end
