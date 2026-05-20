/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # Default basis of `HolomorphicOneForm X`

A canonical `Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)` extracted
via `Module.finBasis` from the unconditional finite-dimensionality
provided by `DiskChartCover.holomorphicOneFormFiniteDim_holds`.

The genus `JacobianChallenge.genus X` is by definition
`Module.finrank ℂ (HolomorphicOneForm X)`, so the basis's index type
`Fin (Module.finrank ℂ ...)` is definitionally `Fin (genus X)`.

This default basis is the canonical choice for downstream constructions
(notably the canonical analytic Jacobian) that should not expose a
basis argument at the type level.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Default basis of `HolomorphicOneForm X`** via `Module.finBasis`.
Finite-dimensionality is unconditional on any compact connected complex
1-manifold (via `DiskChartCover.holomorphicOneFormFiniteDim_holds`),
so the basis exists unconditionally. -/
noncomputable def defaultHolomorphicOneFormBasis :
    Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  -- `Module.finBasis ℂ V` produces a basis indexed by `Fin (Module.finrank ℂ V)`.
  -- `genus X = Module.finrank ℂ (HolomorphicOneForm X)` by definition, so the
  -- index type matches.
  exact Module.finBasis ℂ (HolomorphicOneForm X)

end JacobianChallenge

end
