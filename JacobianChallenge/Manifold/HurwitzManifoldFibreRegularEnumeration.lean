/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzManifoldFibreRegular
import JacobianChallenge.Manifold.HurwitzManifoldFibreEnumeration

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold Hurwitz fibre enumeration + regularity packaging

Combines chip 3d-11 (manifold fibre enumeration: image + distinctness)
with chip 3d-19 (f-regularity at chart-target points with AnalyticAt
hypothesis) into a single consumable theorem for the trace-extension
chip arc.

For `f, z₀, α, ζ, k, ξ` (ξ ≠ 0) with the chart-target / planar
distinctness / planar AnalyticAt + non-vanishing-deriv hypotheses, the
k preimage points `(chartAt ℂ z₀).symm (φ(ζ^j ξ))` are:

* distinct,
* all in `f.regularSet` (so each has a local sheet data for `holTraceAt`),
* all map under `f.toRiemannSphere` to
  `(chartAt ℂ (f z₀)).symm (ξ^k + w₀)`.

No `sorry`, no `axiom`. -/

open Filter Topology Set
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold Hurwitz fibre enumeration + regularity.** -/
theorem manifold_hurwitz_fibre_enumeration_regular
    (f : MeromorphicNonzero X) (z₀ : X)
    {φ : ℂ → ℂ} {ζ : ℂ} {k : ℕ} {ξ : ℂ}
    (h_target_z : ∀ j ∈ Finset.range k, φ (ζ ^ j * ξ) ∈ (chartAt ℂ z₀).target)
    (h_src_y : ∀ j ∈ Finset.range k,
      f.toRiemannSphere ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ)))
        ∈ (chartAt ℂ (f.toRiemannSphere z₀)).source)
    (h_planar : ∀ j ∈ Finset.range k,
      f.chartPullback z₀ (φ (ζ ^ j * ξ))
        - f.chartPullback z₀ ((chartAt ℂ z₀) z₀) = ξ ^ k)
    (h_planar_distinct : ∀ j₁ ∈ Finset.range k, ∀ j₂ ∈ Finset.range k,
      j₁ ≠ j₂ → φ (ζ ^ j₁ * ξ) ≠ φ (ζ ^ j₂ * ξ))
    (h_g_an : ∀ j ∈ Finset.range k,
      AnalyticAt ℂ (f.chartPullback z₀) (φ (ζ ^ j * ξ)))
    (h_g_deriv_ne : ∀ j ∈ Finset.range k,
      deriv (f.chartPullback z₀) (φ (ζ ^ j * ξ)) ≠ 0) :
    (∀ j ∈ Finset.range k,
      f.toRiemannSphere ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ)))
        = (chartAt ℂ (f.toRiemannSphere z₀)).symm
            (ξ ^ k + f.chartPullback z₀ ((chartAt ℂ z₀) z₀))) ∧
    (∀ j₁ ∈ Finset.range k, ∀ j₂ ∈ Finset.range k, j₁ ≠ j₂ →
      ((chartAt ℂ z₀).symm (φ (ζ ^ j₁ * ξ)) : X)
        ≠ (chartAt ℂ z₀).symm (φ (ζ ^ j₂ * ξ))) ∧
    (∀ j ∈ Finset.range k,
      ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ)) : X) ∈ f.regularSet) := by
  obtain ⟨h_image, h_distinct⟩ :=
    f.manifold_hurwitz_fibre_enumeration z₀ h_target_z h_src_y h_planar
      h_planar_distinct
  refine ⟨h_image, h_distinct, ?_⟩
  intro j hj
  exact f.manifold_fibre_regular_at_chart_point z₀ (h_target_z j hj)
    (h_g_an j hj) (h_g_deriv_ne j hj)

end MeromorphicNonzero
end JacobianChallenge

end
