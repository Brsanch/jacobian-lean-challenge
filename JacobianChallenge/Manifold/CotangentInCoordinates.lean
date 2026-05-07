/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import JacobianChallenge.Manifold.Cotangent

set_option diagnostics.threshold 100

/-! # `inCotangentCoordinates`: cotangent analogue of `inTangentCoordinates`

This file mirrors the mathlib construction
`Mathlib.Geometry.Manifold.VectorBundle.Tangent.inTangentCoordinates`
for the cotangent bundle defined in `JacobianChallenge.Manifold.Cotangent`.

Given two `C^1` manifolds `M` (modelled on `(E, H)` via `I`) and
`M'` (modelled on `(E', H')` via `I'`), a parametrising space `N`,
two functions `f : N → M`, `g : N → M'` and a section
`ϕ : N → (E →L[𝕜] 𝕜) →L[𝕜] (E' →L[𝕜] 𝕜)` (which one should think of as a
family of continuous linear maps from the cotangent space at `f x` to the
cotangent space at `g x`, with `CotangentSpace` unfolded so that the type
is independent of `f` and `g`), the function
`inCotangentCoordinates I I' f g ϕ x₀ x` re-expresses `ϕ x` in the
trivialisations of the cotangent bundles around `f x₀` and `g x₀` by
pre/post-composing with the appropriate cotangent coordinate changes.

This is the cotangent analogue needed when wanting to apply
`ContMDiff`-of-derivative lemmas to the cotangent direction, e.g. for
`SmoothOneForm.pullback`.
-/

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']
  {N : Type*}

/-- `inCotangentCoordinates I I' f g ϕ x₀ x` rewrites a continuous linear map
`ϕ x` between the cotangent fibres at `f x` and `g x` in the
trivialisations of the cotangent bundles around `f x₀` and `g x₀`.

Concretely, it is `ContinuousLinearMap.inCoordinates` applied to the
fibre-data of `cotangentBundleCore I M` and `cotangentBundleCore I' M'`.
The fibre type of the cotangent bundle of `M` is `E →L[𝕜] 𝕜` (as a
`CotangentSpace`-unfolded continuous linear map).

This is the cotangent analogue of `inTangentCoordinates`. Once the
hom-bundle smoothness machinery in mathlib is used, families of cotangent
covectors expressed via `inCotangentCoordinates` interact with
`ContMDiffAt.mfderiv`-style results in the same way that
`inTangentCoordinates` does for tangent vectors. -/
def inCotangentCoordinates (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H')
    [ChartedSpace H M] [ChartedSpace H' M']
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (f : N → M) (g : N → M')
    (ϕ : N → (E →L[𝕜] 𝕜) →L[𝕜] (E' →L[𝕜] 𝕜)) :
    N → N → (E →L[𝕜] 𝕜) →L[𝕜] (E' →L[𝕜] 𝕜) :=
  fun x₀ x =>
    inCoordinates (E →L[𝕜] 𝕜) (CotangentSpace I) (E' →L[𝕜] 𝕜) (CotangentSpace I')
      (f x₀) (f x) (g x₀) (g x) (ϕ x)

/-- Rewriting `inCotangentCoordinates` via `cotangentBundleCore`'s coordinate
changes. This is the cotangent analogue of `inTangentCoordinates_eq` and
follows immediately from `VectorBundleCore.inCoordinates_eq`. -/
theorem inCotangentCoordinates_eq
    (f : N → M) (g : N → M')
    (ϕ : N → (E →L[𝕜] 𝕜) →L[𝕜] (E' →L[𝕜] 𝕜)) {x₀ x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source)
    (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inCotangentCoordinates I I' f g ϕ x₀ x =
      ((cotangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x)).comp
        ((ϕ x).comp <|
          (cotangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x)) :=
  (cotangentBundleCore I M).inCoordinates_eq (cotangentBundleCore I' M') (ϕ x) hx hy

end
