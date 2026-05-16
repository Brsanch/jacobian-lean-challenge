/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzFibreImageIdentity
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level fibre-image identity via Hurwitz parameterization

Lifts `hurwitz_fibre_image_eq` (chip 3d-7, planar) through
`(chartAt ℂ z₀).symm` to identify the source-manifold point
`(chartAt ℂ z₀).symm (φ (ζ^j · ξ))` as a preimage under
`f.toRiemannSphere` of the target-manifold point
`(chartAt ℂ (f z₀)).symm (ξ^k + w₀)`.

Caller supplies:
* `h_target_z` — `φ (ζ^j · ξ) ∈ (chartAt ℂ z₀).target` (so we can apply
  `(chartAt ℂ z₀).symm`).
* `h_planar` — the planar fibre-image identity from chip 3d-7.
* `h_src_y` — the lifted point `y := f.toRiemannSphere ((chartAt ℂ z₀).symm
  (φ (ζ^j · ξ)))` is in the chart source at `f z₀`.

The third hypothesis is supplied by downstream chips via continuity of
`f.toRiemannSphere` (small-disc argument shrinking around `z₀`).

No `sorry`, no `axiom`. -/

open Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold-level fibre-image identity** via Hurwitz parameterization.

Given the planar identity `g(φ(ζ^j · ξ)) - w₀ = ξ^k` (= `h_planar`) and
the source-chart-target containment, the lifted point
`(chartAt ℂ z₀).symm (φ (ζ^j · ξ))` maps under `f.toRiemannSphere` to
the target-chart-lift of `ξ^k + w₀`. -/
theorem manifold_fibre_image_eq
    (f : MeromorphicNonzero X) (z₀ : X)
    {φ : ℂ → ℂ} {ζ : ℂ} {k j : ℕ} {ξ : ℂ}
    (_h_target_z : φ (ζ ^ j * ξ) ∈ (chartAt ℂ z₀).target)
    (h_src_y :
      f.toRiemannSphere ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ)))
        ∈ (chartAt ℂ (f.toRiemannSphere z₀)).source)
    (h_planar :
      f.chartPullback z₀ (φ (ζ ^ j * ξ))
        - f.chartPullback z₀ ((chartAt ℂ z₀) z₀) = ξ ^ k) :
    f.toRiemannSphere ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ)))
      = (chartAt ℂ (f.toRiemannSphere z₀)).symm
          (ξ ^ k + f.chartPullback z₀ ((chartAt ℂ z₀) z₀)) := by
  set y := f.toRiemannSphere ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ))) with hy_def
  set w₀ := f.chartPullback z₀ ((chartAt ℂ z₀) z₀) with hw₀_def
  -- Unfold `chartPullback`: `g x = (chartAt ℂ (f z₀)) (f ((chartAt ℂ z₀).symm x))`.
  have h_g_unfold :
      f.chartPullback z₀ (φ (ζ ^ j * ξ))
        = (chartAt ℂ (f.toRiemannSphere z₀)) y := rfl
  -- From h_planar: `g(...) = ξ^k + w₀`.
  have h_g_eq : f.chartPullback z₀ (φ (ζ ^ j * ξ)) = ξ ^ k + w₀ := by
    have := h_planar
    linear_combination this
  -- Hence `(chartAt ℂ (f z₀)) y = ξ^k + w₀`.
  have h_chart_y : (chartAt ℂ (f.toRiemannSphere z₀)) y = ξ ^ k + w₀ := by
    rw [← h_g_unfold]; exact h_g_eq
  -- Apply chart-symm: `(chartAt ℂ (f z₀)).symm ((chartAt ℂ (f z₀)) y) = y` because
  -- `y ∈ (chartAt ℂ (f z₀)).source`.
  have h_left_inv :
      (chartAt ℂ (f.toRiemannSphere z₀)).symm
        ((chartAt ℂ (f.toRiemannSphere z₀)) y) = y :=
    (chartAt ℂ (f.toRiemannSphere z₀)).left_inv h_src_y
  -- Rewrite to get `y = (chartAt ℂ (f z₀)).symm (ξ^k + w₀)`.
  calc y
      = (chartAt ℂ (f.toRiemannSphere z₀)).symm
          ((chartAt ℂ (f.toRiemannSphere z₀)) y) := h_left_inv.symm
    _ = (chartAt ℂ (f.toRiemannSphere z₀)).symm (ξ ^ k + w₀) := by
        rw [h_chart_y]

end MeromorphicNonzero
end JacobianChallenge

end
