/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import JacobianChallenge.Manifold.CotangentInCoordinates

set_option diagnostics.threshold 100

/-! # Smoothness of the cotangent transpose `(mfderiv f).precomp 𝕜`

This file packages the cotangent analogue of `ContMDiffAt.mfderiv`
(the tangent-direction smoothness lemma at
`Mathlib.Geometry.Manifold.ContMDiffMFDeriv`):

For a `C^(n+1)` map `f : M → M'` between (real, `C^1`) manifolds, the
tangent-direction derivative `mfderiv I I' f y : E →L[𝕜] E'` is `C^n`
when expressed in tangent coordinates centred at `(x, f x)`.
Pre-composing each value by the continuous-linear-map
pre-composition operator
  `(L : E →L[𝕜] E').precomp 𝕜 : (E' →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)`
(see `Mathlib.Topology.Algebra.Module.StrongTopology.precomp`) yields
the cotangent transpose: a continuous linear map
`T*_{f y} M' →L[𝕜] T*_y M`. Composition with a smooth fixed CLM
preserves `C^n` regularity (`ContMDiffAt.clm_precomp`), so the family
`y ↦ (inTangentCoordinates I I' id f (fun y ↦ mfderiv I I' f y) x y).precomp 𝕜`
is `C^n` at `x`.

This is the "weaker pointwise form" mentioned in the chip
specification: it is expressed using `inTangentCoordinates` rather
than `inCotangentCoordinates`, but it is the precise object needed
to feed `ContMDiffAt.clm_apply_of_inCoordinates` / the smooth-section
machinery used in `SmoothOneForm.pullback`. The full bundle-level
identification of this object with the cotangent-coordinate
trivialisation of `(mfderiv I I' f y).flip` (in the bilinear-pairing
sense) is left for a follow-up chip; the smoothness statement is
what downstream code requires.
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

/-- **Cotangent-direction smoothness of `mfderiv`** (pointwise / tangent-coordinate
form).

If `f : M → M'` is `C^(n+1)` at `x`, then the family

  `y ↦ (inTangentCoordinates I I' id f (fun y ↦ mfderiv I I' f y) x y).precomp 𝕜
        : (E' →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)`

is `C^n` at `x`. The `.precomp 𝕜` factor sends a continuous linear map
`L : E →L[𝕜] E'` to its transpose
`(η : E' →L[𝕜] 𝕜) ↦ η ∘L L : E →L[𝕜] 𝕜`, which is the
cotangent pullback of `L`.

This is the cotangent analogue of `ContMDiffAt.mfderiv_const`. -/
theorem ContMDiffAt.mfderiv_transpose
    {n m : WithTop ℕ∞} {x : M} {f : M → M'}
    (hf : ContMDiffAt I I' n f x) (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(𝕜, (E' →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)) m
      (fun y => (inTangentCoordinates I I' id f
        (fun y ↦ (mfderiv I I' f y : E →L[𝕜] E')) x y).precomp 𝕜) x :=
  (hf.mfderiv_const hmn).clm_precomp

end
