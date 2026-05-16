/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzFibreInjective
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level fibre-point distinctness via Hurwitz parameterization

Lifts `hurwitz_fibre_distinct_eventually` (chip 3d-8, planar) through
`(chartAt ℂ z₀).symm`. The chart-symm is injective on the chart target,
so distinct inputs in the target give distinct manifold points.

No `sorry`, no `axiom`. -/

open Filter Topology
open scoped Manifold

namespace JacobianChallenge
namespace Manifold

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Manifold-level fibre-point distinctness.**

If `φ(ζ^j₁ ξ), φ(ζ^j₂ ξ) ∈ (chartAt ℂ z₀).target` and
`φ(ζ^j₁ ξ) ≠ φ(ζ^j₂ ξ)` (the planar distinctness), then the lifted
manifold points are distinct:

  `(chartAt ℂ z₀).symm (φ (ζ^j₁ ξ)) ≠ (chartAt ℂ z₀).symm (φ (ζ^j₂ ξ))`. -/
theorem manifold_fibre_point_distinct
    (z₀ : X) {φ : ℂ → ℂ} {ζ : ℂ} {k j₁ j₂ : ℕ} {ξ : ℂ}
    (h_target_z_j₁ : φ (ζ ^ j₁ * ξ) ∈ (chartAt ℂ z₀).target)
    (h_target_z_j₂ : φ (ζ ^ j₂ * ξ) ∈ (chartAt ℂ z₀).target)
    (h_planar_ne : φ (ζ ^ j₁ * ξ) ≠ φ (ζ ^ j₂ * ξ)) :
    ((chartAt ℂ z₀).symm (φ (ζ ^ j₁ * ξ)) : X)
      ≠ (chartAt ℂ z₀).symm (φ (ζ ^ j₂ * ξ)) := by
  -- `(chartAt ℂ z₀).symm` is injective on the chart target.
  intro h_eq
  apply h_planar_ne
  -- Apply `chartAt ℂ z₀` to both sides; use right-inverse on target.
  have h_app : (chartAt ℂ z₀) ((chartAt ℂ z₀).symm (φ (ζ ^ j₁ * ξ)))
      = (chartAt ℂ z₀) ((chartAt ℂ z₀).symm (φ (ζ ^ j₂ * ξ))) := by
    rw [h_eq]
  rwa [(chartAt ℂ z₀).right_inv h_target_z_j₁,
       (chartAt ℂ z₀).right_inv h_target_z_j₂] at h_app

end Manifold
end JacobianChallenge
