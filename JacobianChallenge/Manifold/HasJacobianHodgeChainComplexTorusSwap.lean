/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorus
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus
import JacobianChallenge.Manifold.ComplexTorusZBasisExistence

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain (ℂ ⧸ L)` with swap-orientation (chip 19o)

If the in-tree basis `(lam₁_complexTorus L, lam₂_complexTorus L)` has
**negative orientation** `(star lam₁ · lam₂).im < 0`, we obtain
`HasJacobianHodgeChain (ℂ ⧸ L)` by swapping to `(lam₂, lam₁)` (which
then has positive orientation).

Combined with chip 19n (positive orientation case), this gives
`HasJacobianHodgeChain (ℂ ⧸ L)` from `(star lam₁ · lam₂).im ≠ 0` plus
a sign decision. The "≠ 0" hypothesis is in turn equivalent to ℝ-LI of
the basis (which holds unconditionally via `basisFin2OfL_realLinearIndependent`),
so the remaining gap is just "ℝ-LI ⟹ Im ≠ 0".

## What this file ships

* `hasJacobianHodgeChain_complexTorus_of_orientation_neg` — the
  negative-orientation case via swap.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Symmetry of `IsZBasisOfL`.** Swapping `(lam₁, lam₂)` preserves
the basis property. -/
theorem isZBasisOfL_swap
    {lam₁ lam₂ : ℂ} (h : IsZBasisOfL L lam₁ lam₂) :
    IsZBasisOfL L lam₂ lam₁ := by
  intro z hz
  obtain ⟨m₁, m₂, hm⟩ := h z hz
  refine ⟨m₂, m₁, ?_⟩
  rw [hm]; ring

/-- **`HasJacobianHodgeChain (ℂ ⧸ L)` from negative-orientation input.**
If `(star (lam₁_complexTorus L) · (lam₂_complexTorus L)).im < 0`, then
the swapped pair `(lam₂, lam₁)` has positive orientation, and we apply
chip 19m to it. -/
theorem hasJacobianHodgeChain_complexTorus_of_orientation_neg
    (h_orient_neg :
        (star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im < 0) :
    HasJacobianHodgeChain (ℂ ⧸ L) := by
  apply hasJacobianHodgeChain_complexTorus_of_basis_and_orientation L
    (lam₂_complexTorus L) (lam₁_complexTorus L)
    (lam₂_complexTorus_mem L) (lam₁_complexTorus_mem L)
  · -- IsZBasisOfL L lam₂ lam₁ — symmetric swap.
    exact isZBasisOfL_swap L basisFin2OfL_isZBasisOfL
  · -- 0 < (star lam₂ * lam₁).im = -(star lam₁ * lam₂).im.
    have h_eq :
        (star (lam₂_complexTorus L) * (lam₁_complexTorus L)).im
        = -(star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im := by
      rw [show star (lam₂_complexTorus L) * (lam₁_complexTorus L)
            = star (star (lam₁_complexTorus L) * (lam₂_complexTorus L)) from by
              rw [StarMul.star_mul, star_star]]
      exact Complex.conj_im _
    linarith

end ComplexTorus

end JacobianChallenge

end
