/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothOneForm
import JacobianChallenge.Manifold.CotangentInCoordinates
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import JacobianChallenge.Manifold.MFDerivTranspose
import JacobianChallenge.Manifold.CotangentPullbackBridge
import JacobianChallenge.Manifold.CotangentTangentBridge

set_option diagnostics.threshold 100

/-! # Pullback of a smooth 1-form along a smooth map

Given a `C^∞` map `f : M → M'` between real `C^1`-manifolds, this file
constructs the pullback `f^* : SmoothOneForm I' M' →ₗ[ℝ] SmoothOneForm I M`.

Pointwise the construction is the standard one:
`(f^* om) x = (om (f x)) ∘L (mfderiv I I' f x)`.

The smoothness of the resulting section is established by reducing to
chart-coordinates via `cotangentSection_contMDiffAt_iff`
(`CotangentBundleSmoothness.lean`), then matching the chart-coordinate
representative — on a neighbourhood of any base point — with the
`inCotangentCoordinates`-form coming out of `MFDerivTranspose.lean` via the
bridge identity `pullback_section_in_cotangent_coordinates_apply`
(`CotangentPullbackBridge.lean`). The resulting CLM-of-CLM smoothness statement
combines `ContMDiffAt.mfderiv_transpose` and the smoothness of `om` (transported
through `f`) via `ContMDiffAt.clm_apply` on continuous-linear-map values.
-/

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

namespace SmoothOneForm

/-- Pointwise pullback of a covector field along `f`: at `x : M`, the value is
the precomposition of `om (f x) : CotangentSpace I' (f x)` with the mfderiv of
`f` at `x`. -/
def pullbackFun (f : M → M') (om : ∀ y : M', CotangentSpace I' y) (x : M) :
    CotangentSpace I x :=
  (om (f x)).comp (mfderiv I I' f x)

@[simp] theorem pullbackFun_apply
    (f : M → M') (om : ∀ y : M', CotangentSpace I' y) (x : M) :
    pullbackFun (I := I) (I' := I') f om x =
      (om (f x)).comp (mfderiv I I' f x) := rfl

/-- Pullback of smooth 1-forms is additive at the level of underlying
functions. -/
theorem pullbackFun_add
    (f : M → M') (ω₁ ω₂ : ∀ y : M', CotangentSpace I' y) :
    pullbackFun (I := I) (I' := I') f (fun y => ω₁ y + ω₂ y) =
      fun x => pullbackFun (I := I) (I' := I') f ω₁ x +
        pullbackFun (I := I) (I' := I') f ω₂ x := by
  funext x
  simp only [pullbackFun]
  exact ContinuousLinearMap.add_comp _ _ _

/-- Pullback of smooth 1-forms is `ℝ`-linear at the level of underlying
functions. -/
theorem pullbackFun_smul
    (f : M → M') (c : ℝ) (om : ∀ y : M', CotangentSpace I' y) :
    pullbackFun (I := I) (I' := I') f (fun y => c • om y) =
      fun x => c • pullbackFun (I := I) (I' := I') f om x := by
  funext x
  simp only [pullbackFun]
  exact ContinuousLinearMap.smul_comp _ _ _

/-- **Smoothness of the pullback section.**

If `f : M → M'` is `C^∞` and `om` is a `C^∞` section of the cotangent bundle of
`M'`, then the pointwise pullback `x ↦ (om (f x)).comp (mfderiv f x)` is a `C^∞`
section of the cotangent bundle of `M`.

The proof reduces to a chart-coordinate statement by
`cotangentSection_contMDiffAt_iff` and identifies the chart-coordinate
representative on a neighbourhood of any base point with the
`inCotangentCoordinates` form provided by the bridge identity, after which the
combined smoothness follows from `ContMDiffAt.mfderiv_transpose` and a
`ContMDiffAt.clm_apply` step against the smoothly-transported covector
`om (f x)` (read in `M'`-chart coordinates around `f x₀`). -/
theorem contMDiff_pullbackSection
    (f : M → M') (hf : ContMDiff I I' ⊤ f)
    (om : ∀ y : M', CotangentSpace I' y)
    (hom : ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] ℝ)) ⊤
      (fun y => TotalSpace.mk' (E' →L[ℝ] ℝ) y (om y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ⊤
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ) x
        (pullbackFun (I := I) (I' := I') f om x)) := by
  -- Pointwise reduction (ContMDiff is definitionally ∀ x, ContMDiffAt).
  intro x₀
  rw [cotangentSection_contMDiffAt_iff]
  -- Goal: smoothness at `x₀` of the chart-coord representative
  --   x ↦ (cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x
  --        ((om (f x)).comp (mfderiv I I' f x))
  -- Step 1: write the chart-coord representative on a neighbourhood of `x₀` via
  -- the bridge identity.
  have hx_nhds : ∀ᶠ x in 𝓝 x₀, x ∈ (chartAt H x₀).source :=
    (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  have hfx_nhds : ∀ᶠ x in 𝓝 x₀, f x ∈ (chartAt H' (f x₀)).source := by
    have h0 : f x₀ ∈ (chartAt H' (f x₀)).source := mem_chart_source H' (f x₀)
    exact (hf.continuous.continuousAt) ((chartAt H' (f x₀)).open_source.mem_nhds h0)
  -- Bridge equality on the joint neighbourhood.
  have hEq :
      (fun x => (cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x
          (pullbackFun (I := I) (I' := I') f om x))
        =ᶠ[𝓝 x₀]
      (fun x =>
        inCotangentCoordinates (I := I') (I' := I) f (id : M → M)
            (fun y : M => (ContinuousLinearMap.compL ℝ E E' ℝ).flip
              (mfderiv I I' f y))
            x₀ x
            ((cotangentBundleCore I' M').coordChange
                (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))) := by
    refine (hx_nhds.and hfx_nhds).mono ?_
    rintro x ⟨hx, hfx⟩
    exact pullback_section_in_cotangent_coordinates_apply
      (I := I) (I' := I') f (om (f x)) x x₀ hx hfx
  -- It suffices to prove smoothness of the RHS.
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hEq
  -- Step 2: smoothness of the RHS.
  -- Unfold `inCotangentCoordinates` and split into CLM-apply.
  -- The RHS is: `inCoordinates _ _ _ _ (f x₀) (f x) (id x₀) (id x) (φ x)` applied
  -- to the cocycle-shifted covector. We split via `ContMDiffAt.clm_apply`:
  --  - smoothness of the CLM family in `x` (from `mfderiv_transpose`-transported);
  --  - smoothness of the input covector (from `hom` transported via `f`).
  -- The chip's CLM family for `mfderiv_transpose` is in *tangent* coordinates;
  -- `inCotangentCoordinates` packages the cotangent coordinate change. Identify
  -- via `inCotangentCoordinates` unfolding.
  -- Smoothness of input covector: `cotangentSection_contMDiffAt_iff` applied to `om`
  -- at `f x₀`, transported by `hf.contMDiffAt`.
  have hom_at : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] ℝ) ⊤
      (fun y : M' => (cotangentBundleCore I' M').coordChange
        (achart H' y) (achart H' (f x₀)) y (om y)) (f x₀) := by
    have := (cotangentSection_contMDiffAt_iff (n := (⊤ : WithTop ℕ∞)) om
      (x₀ := f x₀)).mp hom.contMDiffAt
    exact this
  have hom_at_M : ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] ℝ) ⊤
      (fun x : M => (cotangentBundleCore I' M').coordChange
        (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x))) x₀ :=
    hom_at.comp x₀ hf.contMDiffAt
  -- Smoothness of the CLM family.
  have hT : ContMDiffAt I 𝓘(ℝ, (E' →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) ⊤
      (fun y => (ContinuousLinearMap.compL ℝ E E' ℝ).flip
        (inTangentCoordinates I I' id f
          (fun y ↦ (mfderiv I I' f y : E →L[ℝ] E')) x₀ y)) x₀ := by
    have hle : (⊤ : WithTop ℕ∞) + 1 ≤ (⊤ : WithTop ℕ∞) := by
      simp
    exact ContMDiffAt.mfderiv_transpose (I := I) (I' := I') (M := M) (M' := M')
      (n := ⊤) (m := ⊤) (x := x₀) (f := f) hf.contMDiffAt hle
  -- Identify the CLM family with the `inCotangentCoordinates` form.
  -- This is the `inCotangentCoordinates`-vs-`inTangentCoordinates` identification,
  -- which follows because `cotangentBundleCore.coordChange` is by definition
  -- precomposition with the tangent transition (see `Cotangent.lean`).
  -- For the present chip we package this identification as `clm_apply`-shaped
  -- smoothness directly.
  -- Fall through to: smoothness of the bilinear pairing applied to (CLM, covector).
  have hApp : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ⊤
      (fun x : M =>
        ((ContinuousLinearMap.compL ℝ E E' ℝ).flip
          (inTangentCoordinates I I' id f
            (fun y ↦ (mfderiv I I' f y : E →L[ℝ] E')) x₀ x))
          ((cotangentBundleCore I' M').coordChange
            (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))) x₀ :=
    hT.clm_apply hom_at_M
  -- Match this against the goal `inCotangentCoordinates`-form. By definitional
  -- unfolding `inCotangentCoordinates I' I f id (fun y => (compL).flip (mfderiv f y)) x₀ x`
  -- equals `inCoordinates _ (CotangentSpace I') _ (CotangentSpace I) (f x₀) (f x) x₀ x ((compL).flip (mfderiv f x))`.
  -- This `inCoordinates` is by mathlib's definition the composition of cotangent
  -- coordinate changes with the CLM-data. Pre-/post-composing with cotangent core
  -- coordChanges agrees with pre-/post-composing with tangent transitions in the
  -- transposed form, which is the *definition* of the cotangent core in
  -- `Cotangent.lean`. Hence the `inTangentCoordinates`-package coincides with the
  -- `inCotangentCoordinates`-package after `(compL).flip`.
  -- We finish by `congr_of_eventuallyEq` against this identification.
  refine hApp.congr_of_eventuallyEq ?_
  -- Eventually identify the two CLM-apply expressions.
  refine (hx_nhds.and hfx_nhds).mono ?_
  rintro x ⟨hx, hfx⟩
  -- Goal: `(inCotangentCoordinates I' I f id (fun y => (compL).flip (mfderiv f y)) x₀ x)
  --        ((cotangentBundleCore I' M').coordChange (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))
  --      = ((compL).flip (inTangentCoordinates I I' id f (mfderiv f) x₀ x))
  --        ((cotangentBundleCore I' M').coordChange (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))`.
  -- These coincide by the bridge identity: by `inCotangentCoordinates_eq` and the
  -- definition of `cotangentBundleCore.coordChange` as transpose of the tangent
  -- transition, both sides equal
  --   (cotangentBundleCore I M).coordChange (achart H x) (achart H x₀) x
  --     ((om (f x)).comp (mfderiv I I' f x))
  -- via `pullback_section_in_cotangent_coordinates_apply` (LHS) and a direct
  -- unfolding (RHS). We delegate to the bridge for the LHS and then unfold the
  -- tangent-coordinates form on the RHS.
  -- Beta-reduce both sides (LHS and RHS are both `(fun x => ...) x`):
  show
    (inCotangentCoordinates (I := I') (I' := I) f (id : M → M)
        (fun y : M => (ContinuousLinearMap.compL ℝ E E' ℝ).flip
          (mfderiv I I' f y)) x₀ x)
        ((cotangentBundleCore I' M').coordChange
            (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))
      =
    ((ContinuousLinearMap.compL ℝ E E' ℝ).flip
        (inTangentCoordinates I I' id f
          (fun y => (mfderiv I I' f y : E →L[ℝ] E')) x₀ x))
        ((cotangentBundleCore I' M').coordChange
            (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))
  -- Apply ZZ141's bridge identity directly: it says
  --   `inCotangentCoordinates I' I f id (fun y => (compL).flip (mfderiv f y)) x₀ x η`
  --     = `((compL).flip (inTangentCoordinates I I' id f (mfderiv f) x₀ x)) η`
  -- which is exactly our goal with `η := cotChange_M' (om (f x))`.
  exact inCotangentCoordinates_eq_compL_flip_inTangentCoordinates_apply
    (I := I) (I' := I') (f := f) (x := x) (x₀ := x₀)
    (η := (cotangentBundleCore I' M').coordChange
            (achart H' (f x)) (achart H' (f x₀)) (f x) (om (f x)))
    hx hfx

/-- **Pullback of a smooth 1-form** along a `C^∞` map, as an `ℝ`-linear map
between the spaces of smooth 1-forms. -/
def pullback (f : M → M') (hf : ContMDiff I I' ⊤ f) :
    SmoothOneForm I' M' →ₗ[ℝ] SmoothOneForm I M where
  toFun om :=
    { toFun := pullbackFun (I := I) (I' := I') f (fun y => om y)
      contMDiff_toFun := contMDiff_pullbackSection (I := I) (I' := I') (M := M)
        (M' := M') f hf (fun y => om y) om.contMDiff_toFun }
  map_add' ω₁ ω₂ := by
    apply ContMDiffSection.ext
    intro x
    show pullbackFun (I := I) (I' := I') f (fun y => ω₁ y + ω₂ y) x =
      pullbackFun (I := I) (I' := I') f (fun y => ω₁ y) x +
      pullbackFun (I := I) (I' := I') f (fun y => ω₂ y) x
    rw [pullbackFun_add]
  map_smul' c om := by
    apply ContMDiffSection.ext
    intro x
    show pullbackFun (I := I) (I' := I') f (fun y => c • om y) x =
      c • pullbackFun (I := I) (I' := I') f (fun y => om y) x
    rw [pullbackFun_smul]

@[simp] theorem pullback_apply
    (f : M → M') (hf : ContMDiff I I' ⊤ f) (om : SmoothOneForm I' M') (x : M) :
    (pullback (I := I) (I' := I') f hf om : ∀ y : M, CotangentSpace I y) x =
      (om (f x)).comp (mfderiv I I' f x) := rfl

end SmoothOneForm

end
