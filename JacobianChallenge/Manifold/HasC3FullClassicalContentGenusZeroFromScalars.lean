/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasC3FullClassicalContent X` at genus 0 from SCD alone (g²-scalars route)

At `genus X = 0`, both scalar families of the g²-scalars discharge of
the C3 umbrella are vacuous on the empty index `Fin 0`. So the
umbrella class follows from a SCD witness + an arbitrary (empty) basis.

## What ships

* `HasC3FullClassicalContent.of_genus_zero_scd_scalars` — at `genus
  X = 0`, the C3 umbrella follows from a SCD witness + a basis.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X` at `genus X = 0` from SCD alone,
via the g²-scalars route.** -/
theorem HasC3FullClassicalContent.of_genus_zero_scd_scalars
    (h_g : JacobianChallenge.genus X = 0)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    HasC3FullClassicalContent X := by
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; exact Fin.isEmpty
  apply HasC3FullClassicalContent.of_upperTriangularScalars scd basis_ω
  · intro i _ _; exact isEmptyElim i
  · intro i _ _; exact isEmptyElim i

end JacobianChallenge

end
