/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentInCoordinates
import JacobianChallenge.Manifold.MFDerivTranspose
import Mathlib.Geometry.Manifold.MFDeriv.Basic

set_option diagnostics.threshold 100

/-! # Bridge: chart-coordinate representation of the pullback section

Let `f : M → M'` be a `C^1` map and `η : E' →L[𝕜] 𝕜` a covector at `f x ∈ M'`
in `M'`-chart coordinates around `f x` (e.g., `η = ω (f x)` for a section
`ω : ∀ y : M', CotangentSpace I' y`). The chart-coordinate representative of
the pullback section value `(ω(f x)).comp (mfderiv f x) ∈ T*_x M`, expressed in
the trivialisation of the cotangent bundle of `M` around `x₀ : M`, equals the
`inCotangentCoordinates`-form whose CLM-data is the pre-composition family
`y ↦ (compL).flip (mfderiv f y)`, applied to the cotangent-`M'`-cocycle-shifted
covector at `f x`.

This bridges the `inTangentCoordinates`-form coming out of
`ContMDiffAt.mfderiv_transpose` (`MFDerivTranspose.lean`) with the
`(cotangentBundleCore I M).coordChange`-form required by
`cotangentSection_contMDiffAt_iff` (`CotangentBundleSmoothness.lean`); it is
the "weak-form ↔ section-form" identification deferred in the docstring of
`mfderiv_transpose`.

Note the parameter assignment `(I := I') (I' := I)` in the call to
`inCotangentCoordinates`: that definition's first `ModelWithCorners` slot
controls the *source* fibre of the CLM-data (here: covectors at `f x ∈ M'`,
hence `I'`), and its second slot controls the *target* fibre (here: covectors
at `x ∈ M`, hence `I`). See `CotangentInCoordinates.lean` for the convention.

The cocycle factor on the right cannot be removed without restricting to
`f x = f x₀`; it is the standard gauge ambiguity of writing a pullback in two
different cotangent trivialisations of `M'`. Downstream consumers compose this
identity with smoothness of `mfderiv` and smoothness of the cotangent
transitions to conclude smoothness of the pullback section.
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

/-- Cocycle round-trip on the cotangent bundle: applying the coordinate change
`a → b → a` at the same point returns the original covector. -/
private theorem cotangent_coordChange_cocycle
    (a b : atlas H' M') (x : M')
    (hxa : x ∈ (cotangentBundleCore I' M').baseSet a)
    (hxb : x ∈ (cotangentBundleCore I' M').baseSet b)
    (ξ : E' →L[𝕜] 𝕜) :
    (cotangentBundleCore I' M').coordChange b a x
        ((cotangentBundleCore I' M').coordChange a b x ξ) = ξ := by
  have hcc :=
    (cotangentBundleCore I' M').coordChange_comp a b a x ⟨⟨hxa, hxb⟩, hxa⟩ ξ
  have hself :=
    (cotangentBundleCore I' M').coordChange_self a x hxa ξ
  exact hcc.trans hself

/-- **Bridge identity**: the chart-coord representative (LHS) of the pullback
covector `η.comp (mfderiv f x)` at base point `x₀ : M` equals the
`inCotangentCoordinates`-form of the precomposition family
`y ↦ (compL).flip (mfderiv f y)`, evaluated at the `M'`-cotangent-cocycle-
shifted version of `η`.

The proof is `inCotangentCoordinates_eq` (rewriting the RHS into outer
`M`-cotangent-coordChange ∘ pre-compose-by-`mfderiv` ∘ inner `M'`-cotangent-
coordChange) followed by collapsing the inner `M'`-cotangent cocycle round-
trip on `η`. -/
theorem pullback_section_in_cotangent_coordinates_apply
    (f : M → M') (η : E' →L[𝕜] 𝕜) (x x₀ : M)
    (hx : x ∈ (chartAt H x₀).source)
    (hfx : f x ∈ (chartAt H' (f x₀)).source) :
    (cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x
        (η.comp (mfderiv I I' f x))
      =
    inCotangentCoordinates (I := I') (I' := I) f (id : M → M)
        (fun y : M => (ContinuousLinearMap.compL 𝕜 E E' 𝕜).flip
          (mfderiv I I' f y))
        x₀ x
        ((cotangentBundleCore I' M').coordChange
            (achart H' (f x)) (achart H' (f x₀)) (f x) η) := by
  -- Hypotheses for `inCotangentCoordinates_eq`: with `(I := I') (I' := I)`,
  -- `(f := f)` (M-source-position), `(g := id : M → M)`, the `f`-side hypothesis
  -- is `f x ∈ (chartAt H' (f x₀)).source` (= `hfx`), and the `g`-side
  -- hypothesis becomes `id x ∈ (chartAt H (id x₀)).source = (chartAt H x₀).source`,
  -- which is `hx` after `id` reduces.
  have hidx : (id : M → M) x ∈ (chartAt H ((id : M → M) x₀)).source := by
    simpa using hx
  -- Apply `inCotangentCoordinates_eq` to rewrite the RHS.
  rw [inCotangentCoordinates_eq (I := I') (I' := I) (f := f) (g := id)
      (ϕ := fun y : M => (ContinuousLinearMap.compL 𝕜 E E' 𝕜).flip
        (mfderiv I I' f y))
      (x₀ := x₀) (x := x) hfx hidx]
  -- The RHS is now
  --   ((cotangentBundleCore I M).coordChange (achart H (id x)) (achart H (id x₀)) (id x)).comp
  --     (((compL.flip) (mfderiv f x)).comp <|
  --       (cotangentBundleCore I' M').coordChange (achart H' (f x₀)) (achart H' (f x)) (f x))
  -- applied to `(cotangentBundleCore I' M').coordChange (achart H' (f x)) (achart H' (f x₀)) (f x) η`.
  -- Simplify `id` and unfold `.comp`-application.
  simp only [Function.id_def, id_eq, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  -- Now both sides have an outer `(cotangentBundleCore I M).coordChange (achart H x)
  -- (achart H x₀) x` applied to a covector. Reduce to equality of inputs.
  congr 1
  -- Goal: `η.comp (mfderiv f x) =
  --   ((cotangentBundleCore I' M').coordChange (achart H' (f x₀)) (achart H' (f x)) (f x)
  --       ((cotangentBundleCore I' M').coordChange (achart H' (f x)) (achart H' (f x₀)) (f x) η))
  --     ∘L mfderiv f x`.
  -- Collapse the inner cocycle round-trip via `cotangent_coordChange_cocycle`.
  have hxa : f x ∈ (cotangentBundleCore I' M').baseSet (achart H' (f x)) :=
    mem_chart_source H' (f x)
  have hxb : f x ∈ (cotangentBundleCore I' M').baseSet (achart H' (f x₀)) :=
    hfx
  have hcoc := cotangent_coordChange_cocycle (I' := I') (M' := M')
    (achart H' (f x)) (achart H' (f x₀)) (f x) hxa hxb η
  -- `hcoc : (cotangentBundleCore I' M').coordChange (achart H' (f x₀)) (achart H' (f x)) (f x)
  --   ((cotangentBundleCore I' M').coordChange (achart H' (f x)) (achart H' (f x₀)) (f x) η) = η`.
  rw [hcoc]

end
