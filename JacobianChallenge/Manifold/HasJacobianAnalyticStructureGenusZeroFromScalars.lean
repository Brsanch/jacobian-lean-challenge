/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` at genus 0 from the SCD alone

At `genus X = 0`, both scalar families (`g(g − 1)/2` bilinear +
`g(g + 1)/2` sesquilinear) of
`HasJacobianAnalyticStructure.of_upperTriangularScalars` are empty
(`Fin 0` is empty, so `∀ i < j, ...` and `∀ i ≤ j, ...` over `Fin (genus X)`
are vacuously true). The constructor then fires from just the SCD atom.

This validates that the g²-scalar route specialises correctly to the
unconditional genus-0 route at `g = 0`.

## What ships

* `HasJacobianAnalyticStructure.of_genus_zero_scd` — at `genus X = 0`,
  HJAS follows from a SCD witness alone.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` at `genus X = 0` from a SCD
witness.** -/
theorem HasJacobianAnalyticStructure.of_genus_zero_scd
    (h_g : JacobianChallenge.genus X = 0)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) :
    HasJacobianAnalyticStructure X := by
  haveI : IsEmpty (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; exact Fin.isEmpty
  apply HasJacobianAnalyticStructure.of_upperTriangularScalars scd basis_ω
  · -- Strict-upper Q vanishing: vacuous on empty index.
    intro i _ _
    exact isEmptyElim i
  · -- Upper Petersson identities: vacuous on empty index.
    intro i _ _
    exact isEmptyElim i

end JacobianChallenge

end
