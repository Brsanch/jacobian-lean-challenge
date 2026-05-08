/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez

Chip ZZ166: unconditional `h_topo` discharge.

Combines:
* `h_topo_of_h_path` from `PreconnectedFromFiniteComplement.lean` (ZZ159) —
  reduces preconnectedness of `Cᶜ` to path-connectedness of `Cᶜ`.
* `isPathConnected_compl_finite_of_connected_chartedSpace_complex` from
  `PathConnectedComplFinite.lean` (ZZ165) — the unconditional manifold-lift
  showing `Cᶜ` is path-connected when nonempty, for a connected T2 charted
  space modelled on `ℂ`.

The result: an unconditional `h_topo` for connected complex 1-manifolds.

No `axiom`, no `sorry`.
-/
import JacobianChallenge.Manifold.PreconnectedFromFiniteComplement
import JacobianChallenge.Manifold.PathConnectedComplFinite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

open scoped Manifold Topology

namespace JacobianChallenge.Manifold

/-- **Unconditional `h_topo`.** For a connected, T2 charted space modelled on
`ℂ` with the analytic-smoothness manifold structure, the complement of any
finite set is preconnected. -/
theorem h_topo_holds_unconditional
    {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [T2Space Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) := by
  intro C hC
  by_cases h : (Cᶜ : Set Y) = ∅
  · rw [h]; exact isPreconnected_empty
  · have hne : (Cᶜ : Set Y).Nonempty := Set.nonempty_iff_ne_empty.mpr h
    exact (isPathConnected_compl_finite_of_connected_chartedSpace_complex
      hC hne).isConnected.isPreconnected

end JacobianChallenge.Manifold
