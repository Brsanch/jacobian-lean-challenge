/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzManifoldFibreImage
import JacobianChallenge.Manifold.HurwitzManifoldFibreInjective

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level Hurwitz fibre enumeration

Consolidates the manifold-level fibre-image identity (chip 3d-9) and
distinctness (chip 3d-10) into one consumable theorem: at ξ ≠ 0 near
`0` with all the `φ(ζ^j · ξ)` in the source-chart target and the
lifted manifold points in the f-chart source, the family

  `p_j ξ := (chartAt ℂ z₀).symm (φ (ζ^j · ξ))`,  `j ∈ Finset.range k`

is an injective parameterization of k distinct preimages of
`(chartAt ℂ (f z₀)).symm (ξ^k + w₀)` under `f.toRiemannSphere`.

This is the **packaged manifold-level fibre enumeration** chip that
downstream sheet/cotangent-pullback chips consume.

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

/-- **Manifold-level Hurwitz fibre enumeration.**

For the family `p_j ξ := (chartAt ℂ z₀).symm (φ (ζ^j · ξ))`, `j ∈ Finset.range k`:

* **(Image)**  Each `p_j ξ` maps under `f.toRiemannSphere` to
  `(chartAt ℂ (f z₀)).symm (ξ^k + w₀)`.

* **(Distinctness)**  Distinct `j₁, j₂ ∈ Finset.range k` give distinct
  `p_j₁ ξ ≠ p_j₂ ξ` whenever the planar `φ`-images are distinct (chip
  3d-10's hypothesis form). -/
theorem manifold_hurwitz_fibre_enumeration
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
      j₁ ≠ j₂ → φ (ζ ^ j₁ * ξ) ≠ φ (ζ ^ j₂ * ξ)) :
    (∀ j ∈ Finset.range k,
      f.toRiemannSphere ((chartAt ℂ z₀).symm (φ (ζ ^ j * ξ)))
        = (chartAt ℂ (f.toRiemannSphere z₀)).symm
            (ξ ^ k + f.chartPullback z₀ ((chartAt ℂ z₀) z₀))) ∧
    (∀ j₁ ∈ Finset.range k, ∀ j₂ ∈ Finset.range k, j₁ ≠ j₂ →
      ((chartAt ℂ z₀).symm (φ (ζ ^ j₁ * ξ)) : X)
        ≠ (chartAt ℂ z₀).symm (φ (ζ ^ j₂ * ξ))) := by
  refine ⟨?_, ?_⟩
  · intro j hj
    exact manifold_fibre_image_eq f z₀ (h_target_z j hj)
      (h_src_y j hj) (h_planar j hj)
  · intro j₁ hj₁ j₂ hj₂ hne
    exact Manifold.manifold_fibre_point_distinct (k := k) z₀
      (h_target_z j₁ hj₁) (h_target_z j₂ hj₂)
      (h_planar_distinct j₁ hj₁ j₂ hj₂ hne)

end MeromorphicNonzero
end JacobianChallenge

end
