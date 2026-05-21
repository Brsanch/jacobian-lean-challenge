/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorus
import JacobianChallenge.Manifold.GenericGenusPeriodLatticeInputsComplexTorus
import JacobianChallenge.Manifold.ComplexTorusZBasisExistence

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain (ℂ ⧸ L)` from orientation only (chip 19n)

Specializes chip 19m to the explicit in-tree basis
`(lam₁_complexTorus L, lam₂_complexTorus L)`. The `IsZBasisOfL`
hypothesis is unconditional in tree
(`basisFin2OfL_isZBasisOfL`), leaving the **lattice orientation
condition** as the only remaining input.

The full classical content of `HasJacobianHodgeChain (ℂ ⧸ L)` thus
reduces to:

  `0 < (star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im`

— the standard "positive area" condition on the explicit ℤ-basis
of `L`.

## What this file ships

* `hasJacobianHodgeChain_complexTorus_of_orientation` — the 1-input
  reduction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`HasJacobianHodgeChain (ℂ ⧸ L)` from lattice orientation only.**
Specializes chip 19m to the explicit in-tree basis. The only remaining
classical input is the lattice-orientation condition. -/
theorem hasJacobianHodgeChain_complexTorus_of_orientation
    (h_orient : 0 < (star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im) :
    HasJacobianHodgeChain (ℂ ⧸ L) :=
  hasJacobianHodgeChain_complexTorus_of_basis_and_orientation L
    (lam₁_complexTorus L) (lam₂_complexTorus L)
    (lam₁_complexTorus_mem L) (lam₂_complexTorus_mem L)
    basisFin2OfL_isZBasisOfL
    h_orient

end ComplexTorus

end JacobianChallenge

end
