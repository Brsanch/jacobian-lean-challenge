/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain X` at genus 0 from SCD alone (g²-scalars route)

At `genus X = 0`, the g²-scalars discharge of HJHC collapses to:
* `g(g − 1)/2 = 0` empty strict-upper Q vanishing;
* `g(g + 1)/2 = 0` empty upper-tri Petersson identities.

Both vacuous on `Fin 0`, so HJHC follows from a SCD witness + an
arbitrary (empty) basis.

## What ships

* `HasJacobianHodgeChain.of_genus_zero_scd_scalars` — at `genus X =
  0`, HJHC follows from a SCD witness + a basis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianHodgeChain X` at `genus X = 0` from SCD alone, via the
g²-scalars route.** -/
theorem HasJacobianHodgeChain.of_genus_zero_scd_scalars
    (h_g : JacobianChallenge.genus X = 0)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    HasJacobianHodgeChain X := by
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; exact Fin.isEmpty
  apply HasJacobianHodgeChain.of_upperTriangularScalars scd basis_ω
  · intro i _ _; exact isEmptyElim i
  · intro i _ _; exact isEmptyElim i

end JacobianChallenge

end
