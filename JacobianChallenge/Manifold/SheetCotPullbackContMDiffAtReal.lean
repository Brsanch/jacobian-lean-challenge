/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SheetCotangentPullbackContMDiffAt
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAt
import JacobianChallenge.Manifold.RiemannSphereRealManifold
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent
import JacobianChallenge.Manifold.ContMDiffRealification

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Realified per-sheet cotangent-pullback section smoothness

Companion to `SheetCotangentPullbackContMDiffAt.lean` in the **realified**
bundle. For a smooth-at-`y₀` map `g : Y → X` between complex 1-manifolds
viewed as real `C^∞` manifolds (i.e., `[IsManifold 𝓘(ℝ, ℂ) ⊤ _]`) and a
general `om : SmoothOneForm 𝓘(ℝ, ℂ) X` (e.g.
`realComponent α` or `imagComponent α` for `α : HolomorphicOneForm X`),
the pointwise cotangent pullback

  `y ↦ TotalSpace.mk' (ℂ →L[ℝ] ℝ) y (cotangentPullbackAt g y om)`

is `ContMDiffAt 𝓘(ℝ, ℂ) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ∞` at `y₀`.

The proof scaffold is identical to
`pullbackSection_contMDiffAt_of_localSheet` (`SheetCotangentPullbackContMDiffAt`):
`ContMDiffAt.clm_apply_of_inCoordinates` + cotangent↔tangent inCoordinates
bridge + `ContMDiffAt.mfderiv_transpose`. The only difference is the
field (`ℝ` instead of `ℂ`) and regularity (`⊤` instead of `ω`). The
underlying mathlib lemmas (`inCotangentCoordinates_eq`,
`cotangentBundleCore_coordChange_apply`, `inTangentCoordinates_eq`,
`ContMDiffAt.mfderiv_transpose`) are all field-generic.

Application: feeding `f.localSheetData_at_regular hnc hp_reg`'s sheet
(via its realified `ContMDiffAt ∞` witness from
`Manifold/SourceFiberPathIntegrandChainAtT.lean`'s usage pattern, or
via realification of `f.contMDiffAt_localSheet_g_at_basePoint`) yields
per-sheet realified smoothness at every regular value. This is the
direct building block for `sheetCotPullback`'s smoothness (and hence
for `fStarOmega`'s smoothness on `regularValueSet`).

No `sorry`, no `axiom`. -/

open Set Filter
open scoped Manifold ContDiff Topology
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℝ, ℂ) ⊤ Y]

/-- `⊤ + 1 ≤ ⊤` in `WithTop ℕ∞`. -/
private theorem top_succ_le_top : ((⊤ : WithTop ℕ∞) + 1 : WithTop ℕ∞) ≤ ⊤ := by
  decide

/-- **Regularity-preserving complex-to-real realification.**

Companion to `ContMDiffAt.complex_to_real` (`Manifold/ContMDiffRealification.lean`)
that keeps `ω = ⊤` regularity in the realified bundle instead of dropping to
`∞`. The proof body is identical except for the final omission of the
`of_le (∞ ≤ ω)` regularity-drop step. -/
private theorem ContMDiffAt.complex_to_real_omega
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y]
    {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f x) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨h_cont, h_diff⟩ := hf
  refine ⟨h_cont, ?_⟩
  have h_range_r : range (𝓘(ℝ, ℂ) : ModelWithCorners ℝ ℂ ℂ) = univ := by
    simp [ModelWithCorners.range_eq_univ]
  have h_range_c : range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ := by
    simp [ModelWithCorners.range_eq_univ]
  have h_ext_eq_c : ⇑(extChartAt (𝓘(ℂ, ℂ)) x) = ⇑(chartAt ℂ x) := by
    ext z; simp [extChartAt_coe]
  have h_ext_eq_c_y : ⇑(extChartAt (𝓘(ℂ, ℂ)) (f x)) = ⇑(chartAt ℂ (f x)) := by
    ext z; simp [extChartAt_coe]
  have h_ext_symm_c : ⇑(extChartAt (𝓘(ℂ, ℂ)) x).symm = ⇑(chartAt ℂ x).symm := by
    ext z; simp [extChartAt_coe_symm]
  have h_ext_eq_r : ⇑(extChartAt (𝓘(ℝ, ℂ)) x) = ⇑(chartAt ℂ x) := by
    ext z; simp [extChartAt_coe]
  have h_ext_eq_r_y : ⇑(extChartAt (𝓘(ℝ, ℂ)) (f x)) = ⇑(chartAt ℂ (f x)) := by
    ext z; simp [extChartAt_coe]
  have h_ext_symm_r : ⇑(extChartAt (𝓘(ℝ, ℂ)) x).symm = ⇑(chartAt ℂ x).symm := by
    ext z; simp [extChartAt_coe_symm]
  rw [h_range_r, h_ext_eq_r, h_ext_eq_r_y, h_ext_symm_r]
  rw [h_range_c, h_ext_eq_c, h_ext_eq_c_y, h_ext_symm_c] at h_diff
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  have h_real : ContDiffWithinAt ℝ ω
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) univ ((chartAt ℂ x) x) :=
    ContDiffWithinAt.restrict_scalars (𝕜 := ℝ) h_diff
  exact h_real

/-! ## Realified cotangent↔tangent inCoordinates bridge

Field-generic version of
`cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates` for
`𝕜 := ℝ`. Same proof scaffold: rewrite via `inCotangentCoordinates_eq`
and `inTangentCoordinates_eq`, then reduce via
`cotangentBundleCore_coordChange_apply`. -/

/-- **Pointwise realified cotangent↔tangent inCoordinates bridge.** On
chart-source intersection, the cotangent `inCoordinates` of
`((compL).flip (mfderiv g x))` equals `(compL).flip` of the tangent
`inCoordinates` of `mfderiv g x`, in the realified `𝕜 = ℝ` setting. -/
theorem cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates_real
    (g : Y → X) {y₀ y : Y}
    (hy : y ∈ (chartAt ℂ y₀).source)
    (hgy : g y ∈ (chartAt ℂ (g y₀)).source) :
    ContinuousLinearMap.inCoordinates (ℂ →L[ℝ] ℝ)
      (CotangentSpace (𝓘(ℝ, ℂ)) : X → Type _) (ℂ →L[ℝ] ℝ)
      (CotangentSpace (𝓘(ℝ, ℂ)) : Y → Type _)
      (g y₀) (g y) y₀ y
      ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
        (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y))
    = (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
        (inTangentCoordinates (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) id g
          (fun y => mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) y₀ y) := by
  -- LHS unfolds to `inCotangentCoordinates 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g id _ y₀ y`.
  have h_lhs :
      ContinuousLinearMap.inCoordinates (ℂ →L[ℝ] ℝ)
        (CotangentSpace (𝓘(ℝ, ℂ)) : X → Type _) (ℂ →L[ℝ] ℝ)
        (CotangentSpace (𝓘(ℝ, ℂ)) : Y → Type _)
        (g y₀) (g y) y₀ y
        ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
          (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y))
      = inCotangentCoordinates (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g (id : Y → Y)
          (fun y => (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
            (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y)) y₀ y := rfl
  rw [h_lhs]
  rw [inCotangentCoordinates_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
      (f := g) (g := (id : Y → Y))
      (ϕ := fun y => (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
        (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y))
      (x₀ := y₀) (x := y) hgy (by simpa using hy)]
  rw [inTangentCoordinates_eq (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
      (f := (id : Y → Y)) (g := g)
      (ϕ := fun y => mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y)
      (x₀ := y₀) (x := y) (by simpa using hy) hgy]
  ext η
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    cotangentBundleCore_coordChange_apply]

/-- **Realified bridge, eventually form.** For any `g : Y → X` with
`ContinuousAt g y₀`, the cotangent-inCoordinates and `(compL).flip`-of-
tangent-inCoordinates forms agree in a neighbourhood of `y₀`. -/
private theorem cotangent_inCoordinates_flip_eventually_eq_real
    (g : Y → X) {y₀ : Y} (hg : ContinuousAt g y₀) :
    (fun y : Y =>
      ContinuousLinearMap.inCoordinates (ℂ →L[ℝ] ℝ)
        (CotangentSpace (𝓘(ℝ, ℂ)) : X → Type _) (ℂ →L[ℝ] ℝ)
        (CotangentSpace (𝓘(ℝ, ℂ)) : Y → Type _)
        (g y₀) (g y) y₀ y
        ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
          (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y)))
    =ᶠ[nhds y₀] (fun y : Y =>
      (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
        (inTangentCoordinates (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) id g
          (fun y => mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) y₀ y)) := by
  have h_chart_Y : (chartAt ℂ y₀).source ∈ nhds y₀ :=
    (chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
  have h_chart_X : g ⁻¹' (chartAt ℂ (g y₀)).source ∈ nhds y₀ :=
    hg ((chartAt ℂ (g y₀)).open_source.mem_nhds (mem_chart_source ℂ (g y₀)))
  filter_upwards [h_chart_Y, h_chart_X] with y hy hgy
  exact cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates_real g hy hgy

/-! ## Headline: realified per-sheet pullback section smoothness -/

/-- **Realified per-local-sheet pullback section smoothness.** For
a map `g : Y → X` between complex 1-manifolds (viewed as real
`C^∞` manifolds) with `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g y₀`, and
a smooth real 1-form `om : SmoothOneForm 𝓘(ℝ, ℂ) X`, the section

  `y ↦ TotalSpace.mk' (ℂ →L[ℝ] ℝ) y (cotangentPullbackAt g y om)`

is `ContMDiffAt 𝓘(ℝ, ℂ) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ∞` at
`y₀`. -/
theorem pullbackSection_contMDiffAt_of_localSheet_real
    (g : Y → X) {y₀ : Y} (hg : ContMDiffAt (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤ g y₀)
    (om : SmoothOneForm (𝓘(ℝ, ℂ)) X) :
    ContMDiffAt (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) y
        (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) g y om)) y₀ := by
  -- Recast `cotangentPullbackAt g y om` in `ϕ y (v y)` shape.
  let b₁ : Y → X := g
  let b₂ : Y → Y := id
  let v : ∀ y : Y, CotangentSpace (𝓘(ℝ, ℂ)) (b₁ y) := fun y => om (b₁ y)
  let ϕ : ∀ y : Y,
      CotangentSpace (𝓘(ℝ, ℂ)) (b₁ y) →L[ℝ]
        CotangentSpace (𝓘(ℝ, ℂ)) (b₂ y) :=
    fun y => (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
      (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y)
  have h_eq : ∀ y : Y,
      cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) g y om
        = ϕ y (v y) := by
    intro y
    show ContinuousLinearMap.comp (om (g y))
        (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y)
      = ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
          (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y))
            (om (g y))
    rfl
  have h_funext : (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) y
      (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) g y om))
    = (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) (b₂ y) (ϕ y (v y))) := by
    funext y; rw [h_eq y]; rfl
  rw [h_funext]
  -- ϕ-side smoothness via mfderiv_transpose (field-generic) + bridge.
  have h_phi : ContMDiffAt (𝓘(ℝ, ℂ)) (𝓘(ℝ, (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ))) ⊤
      (fun y : Y => ContinuousLinearMap.inCoordinates (ℂ →L[ℝ] ℝ)
        (CotangentSpace (𝓘(ℝ, ℂ)) : X → Type _) (ℂ →L[ℝ] ℝ)
        (CotangentSpace (𝓘(ℝ, ℂ)) : Y → Type _)
        (b₁ y₀) (b₁ y) (b₂ y₀) (b₂ y) (ϕ y)) y₀ := by
    have h_mfderiv_transpose : ContMDiffAt (𝓘(ℝ, ℂ))
        (𝓘(ℝ, (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ))) ⊤
        (fun y : Y => (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip
          (inTangentCoordinates (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) id g
            (fun y => mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) g y) y₀ y)) y₀ :=
      hg.mfderiv_transpose top_succ_le_top
    have h_bridge :=
      cotangent_inCoordinates_flip_eventually_eq_real (g := g) hg.continuousAt
    exact h_mfderiv_transpose.congr_of_eventuallyEq h_bridge
  -- v-side smoothness: `om` composed with `g` as a total-space-valued map.
  -- `om.contMDiff` is already ⊤ (the `SmoothOneForm` definition uses ⊤),
  -- matching the sheet's realified regularity (preserved via `restrictScalars`).
  have h_v : ContMDiffAt (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) (b₁ y) (v y)) y₀ :=
    om.contMDiff.contMDiffAt.comp y₀ hg
  exact ContMDiffAt.clm_apply_of_inCoordinates (hϕ := h_phi) (hv := h_v)
    (hb₂ := contMDiffAt_id)

/-! ## MeromorphicNonzero specialisation -/

namespace MeromorphicNonzero

universe u

variable {Z : Type u}
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold (𝓘(ℂ, ℂ)) ω Z]

/-- **Per-sheet realified pullback section smoothness at a regular value.**

For a non-constant `f : MeromorphicNonzero Z` and a regular preimage
`p ∈ f.regularSet`, the local sheet
`(f.localSheetData_at_regular hnc hp_reg).g : RiemannSphere → Z`
gives rise to a realified pullback section

  `v ↦ TotalSpace.mk' (ℂ →L[ℝ] ℝ) v
        (sheetCotPullback f hnc hp_reg v om)`

which is `ContMDiffAt 𝓘(ℝ, ℂ) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ∞`
at `v₀ := f.toRiemannSphere p`. -/
theorem sheetCotPullback_contMDiffAt
    (f : MeromorphicNonzero Z)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : Z} (hp_reg : p ∈ f.regularSet)
    (om : SmoothOneForm (𝓘(ℝ, ℂ)) Z) :
    ContMDiffAt (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v
        (f.sheetCotPullback hnc hp_reg v om))
      (f.toRiemannSphere p) := by
  -- Realify the sheet's ω-smoothness, preserving regularity via
  -- `ContMDiffAt_restrictScalars_to_real`.
  have h_sheet_ω : ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
      (f.localSheetData_at_regular hnc hp_reg).g (f.toRiemannSphere p) :=
    f.contMDiffAt_localSheet_g_at_basePoint hnc hp_reg
  have h_sheet_real : ContMDiffAt (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤
      (f.localSheetData_at_regular hnc hp_reg).g (f.toRiemannSphere p) :=
    ContMDiffAt.complex_to_real_omega h_sheet_ω
  -- Apply the headline. sheetCotPullback unfolds to cotangentPullbackAt.
  unfold sheetCotPullback
  exact pullbackSection_contMDiffAt_of_localSheet_real
    (g := (f.localSheetData_at_regular hnc hp_reg).g) h_sheet_real om

end MeromorphicNonzero

end JacobianChallenge

end
