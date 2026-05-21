/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexPairImStarMulFromLinearIndependent
import JacobianChallenge.Manifold.HasJacobianHodgeChainComplexTorusFromNonzero
import JacobianChallenge.Manifold.PeriodLatticeSymplecticBundleComplexTorus

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain (ℂ ⧸ L)` unconditional (chip 19r)

Composes:

* chip 19p (`hasJacobianHodgeChain_complexTorus_of_im_ne_zero`),
  reducing the chain to
  `(star (lam₁_complexTorus L) · (lam₂_complexTorus L)).im ≠ 0`;
* chip 19q (`im_star_mul_ne_zero_of_linearIndependent_pair`),
  reducing nonvanishing of that imaginary part to ℝ-linear
  independence of the pair `(lam₁_complexTorus L, lam₂_complexTorus L)`;
* the in-tree unconditional `basisFin2OfL_realLinearIndependent` from
  `PeriodLatticeSymplecticBundleComplexTorus.lean`, which is the
  ℝ-LI premise on the canonical `Fin 2` ℤ-basis of every discrete
  full-rank ℤ-lattice `L ≤ ℂ`.

The composition makes `HasJacobianHodgeChain (ℂ ⧸ L)` **unconditional**
on every such `L`.

## What this file ships

* `hasJacobianHodgeChain_complexTorus_unconditional` — the headline.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`HasJacobianHodgeChain (ℂ ⧸ L)` unconditional.**

For every discrete full-rank ℤ-lattice `L ≤ ℂ`, the canonical Hodge
chain on the complex torus `ℂ ⧸ L` exists. The remaining classical
input from chip 19p — nonvanishing of `Im(star lam₁ · lam₂)` on the
explicit basis pair — is discharged via chip 19q
(linear-algebraic ℝ-LI ⟹ Im ≠ 0) and
`basisFin2OfL_realLinearIndependent` (the ℝ-LI premise for the
canonical `Fin 2` ℤ-basis). -/
theorem hasJacobianHodgeChain_complexTorus_unconditional :
    HasJacobianHodgeChain (ℂ ⧸ L) := by
  apply hasJacobianHodgeChain_complexTorus_of_im_ne_zero L
  -- Goal: `(star (lam₁_complexTorus L) * (lam₂_complexTorus L)).im ≠ 0`.
  -- Apply chip 19q with the canonical lattice basis ℝ-LI premise.
  exact Complex.im_star_mul_ne_zero_of_linearIndependent_pair
    (basisFin2OfL_realLinearIndependent L)

end ComplexTorus

end JacobianChallenge

end
