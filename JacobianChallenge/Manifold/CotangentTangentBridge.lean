/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentInCoordinates
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option diagnostics.threshold 100

/-! # Bridge: `inCotangentCoordinates` ↔ `(compL).flip ∘ inTangentCoordinates`

For a `C^1` map `f : M → M'`, the cotangent-coordinate representative of the
precomposition family `y ↦ (compL 𝕜 E E' 𝕜).flip (mfderiv f y)` (applied to a
covector `η : E' →L[𝕜] 𝕜`, viewed as the chart-coordinate representative of a
covector at `f x ∈ M'`) coincides with the result of post-composing
`inTangentCoordinates`-rewritten `mfderiv f` with `η`.

Both sides expand under `inCoordinates_eq` (cotangent or tangent) to the same
four-fold composition:

    η ∘L T_{M'}.coordChange (achart H' (f x)) (achart H' (f x₀)) (f x)
       ∘L mfderiv f x
       ∘L T_M.coordChange (achart H x₀) (achart H x) x

since the cotangent transition `cotCore.coordChange a b x` is by definition
precomposition with the *reversed* tangent transition
`T.coordChange b a x` (cf. `Cotangent.lean`).

This is the cleaner replacement for the cocycle-shifted identity in
`CotangentPullbackBridge.lean`: when one is willing to commit to applying both
sides to a single covector `η`, no `M'`-cotangent cocycle round-trip is needed.

Downstream consumers can transport smoothness of the
`inTangentCoordinates`-form (proved in `MFDerivTranspose.lean` via
`ContMDiffAt.mfderiv_const`) directly to the `inCotangentCoordinates`-form by
post-composing pointwise with `(compL).flip`.
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

/-- **Bridge identity** between the cotangent- and tangent-coordinate
representatives of the pullback CLM-data.

Both sides, when applied to a covector `η : E' →L[𝕜] 𝕜`, equal

  `η ∘L T_{M'}.cc(a (f x), a (f x₀), f x) ∘L mfderiv f x ∘L T_M.cc(a x₀, a x, x)`

where `T_M`, `T_{M'}` are the tangent cores of `M`, `M'` and
`a := achart` is the canonical chart-witness map. The LHS reaches this
form via `inCotangentCoordinates_eq` followed by unfolding
`cotangentBundleCore.coordChange a b x = (·).comp (T.cc b a x)`. The RHS
reaches it via `inTangentCoordinates_eq` followed by `compL.flip ξ T = ξ.comp T`. -/
theorem inCotangentCoordinates_eq_compL_flip_inTangentCoordinates_apply
    (f : M → M') (x x₀ : M) (η : E' →L[𝕜] 𝕜)
    (hx : x ∈ (chartAt H x₀).source)
    (hfx : f x ∈ (chartAt H' (f x₀)).source) :
    inCotangentCoordinates (I := I') (I' := I) f (id : M → M)
        (fun y : M => (ContinuousLinearMap.compL 𝕜 E E' 𝕜).flip
          (mfderiv I I' f y))
        x₀ x η
      =
    ((ContinuousLinearMap.compL 𝕜 E E' 𝕜).flip
        (inTangentCoordinates I I' (id : M → M) f
          (fun y : M => (mfderiv I I' f y : E →L[𝕜] E')) x₀ x)) η := by
  -- For `inCotangentCoordinates_eq` on the LHS we need:
  --   `f x ∈ (chartAt H' (f x₀)).source` and
  --   `(id : M→M) x ∈ (chartAt H ((id : M→M) x₀)).source`.
  have hidx : (id : M → M) x ∈ (chartAt H ((id : M → M) x₀)).source := by
    simpa using hx
  -- For `inTangentCoordinates_eq` on the RHS the same two hypotheses are needed
  -- (with the f / id sides swapped to match the (id : M → M, f) parameter order).
  have hidx' : (id : M → M) x ∈ (chartAt H ((id : M → M) x₀)).source := hidx
  -- Rewrite the LHS using `inCotangentCoordinates_eq`.
  rw [inCotangentCoordinates_eq (I := I') (I' := I) (f := f) (g := id)
      (ϕ := fun y : M => (ContinuousLinearMap.compL 𝕜 E E' 𝕜).flip
        (mfderiv I I' f y))
      (x₀ := x₀) (x := x) hfx hidx]
  -- Rewrite the RHS's `inTangentCoordinates` using `inTangentCoordinates_eq`.
  rw [inTangentCoordinates_eq (I := I) (I' := I')
      (f := (id : M → M)) (g := f)
      (ϕ := fun y : M => (mfderiv I I' f y : E →L[𝕜] E'))
      (x₀ := x₀) (x := x) hidx' hfx]
  -- Now both sides are explicit four-fold compositions. Reduce to equality of
  -- application by unfolding `.comp`/`flip`/`compL` everywhere, with `id`-args
  -- collapsed via `id_eq`.
  ext
  simp only [id_eq, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    cotangentBundleCore_coordChange_apply]

end
