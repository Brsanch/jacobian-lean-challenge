/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import JacobianChallenge.Manifold.HurwitzPatchingDataConstruction

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level `LocalSheetData` at every regular point

For `f : MeromorphicNonzero X` with non-constant `f.toRiemannSphere` and
a regular point `x₀ ∈ f.regularSet`, this file constructs

  `LocalSheetData f.toRiemannSphere (f.toRiemannSphere x₀) x₀`

(the structure consumed by `HurwitzPatchingData.ofLocalSheets`) by chart
wrangling around the planar `OpenPartialHomeomorph ℂ ℂ` built in
`MeromorphicNonzeroLocalSheet`.

## Construction outline

Set
* `c := chartAt ℂ x₀`,
* `v₀ := f.toRiemannSphere x₀`, `d := chartAt ℂ v₀`,
* `φ := f.chartPullback_oph hnc hx₀` (planar local biholomorphism).

The trans-composition `c.trans (φ.trans d.symm) : OpenPartialHomeomorph X
RiemannSphere` has underlying function `d.symm ∘ φ ∘ c`.  To make this
agree with `f.toRiemannSphere`, two restrictions are needed:

1. Restrict `φ.source` to lie inside `c.target` (so that `c.symm ∘
   φ.symm` is well-defined and continuous in the inverse direction).
   Achieved by `φ.restrOpen c.target c.open_target`.

2. Further restrict the trans-composition's source to the open subset
   `f.toRiemannSphere ⁻¹' d.source` (so that `d (f.toRiemannSphere x) =
   φ (c x)` is the actual chart pullback, and `d.symm (d (f.toRiemannSphere
   x)) = f.toRiemannSphere x` by `d.left_inv`).  Achieved by another
   `restrOpen`.

The resulting `OpenPartialHomeomorph X RiemannSphere` (call it `M`)
agrees with `f.toRiemannSphere` on its source.  Read off
`LocalSheetData` from `M`'s fields.

## What ships

* `MeromorphicNonzero.manifoldLocalOph` — the manifold-level
  `OpenPartialHomeomorph X RiemannSphere`.
* `MeromorphicNonzero.localSheetData_at_regular` — the headline
  `LocalSheetData` witness at every regular point.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Planar `OpenPartialHomeomorph` at a regular point (chip 6) -/

/-- The planar `OpenPartialHomeomorph ℂ ℂ` packaging the local
biholomorphism of `f.chartPullback x₀` at `(chartAt ℂ x₀) x₀`. -/
noncomputable def chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    OpenPartialHomeomorph ℂ ℂ :=
  let h_an : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
    f.analyticAt_chartPullback x₀
  let h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc hx₀
  let hsd : HasStrictDerivAt (f.chartPullback x₀)
      (deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀)) ((chartAt ℂ x₀) x₀) :=
    h_an.hasStrictDerivAt
  let hsfd : HasStrictFDerivAt (f.chartPullback x₀)
      (ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.mk0 (deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀)) h_dne) :
        ℂ →L[ℂ] ℂ) ((chartAt ℂ x₀) x₀) :=
    hsd.hasStrictFDerivAt_equiv h_dne
  hsfd.toOpenPartialHomeomorph (f.chartPullback x₀)

lemma mem_source_chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    (chartAt ℂ x₀) x₀ ∈ (f.chartPullback_oph hnc hx₀).source := by
  have h_an : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
    f.analyticAt_chartPullback x₀
  have h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc hx₀
  exact (h_an.hasStrictDerivAt.hasStrictFDerivAt_equiv h_dne).mem_toOpenPartialHomeomorph_source

lemma coe_chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    ((f.chartPullback_oph hnc hx₀) : ℂ → ℂ) = f.chartPullback x₀ := by
  have h_an : AnalyticAt ℂ (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) :=
    f.analyticAt_chartPullback x₀
  have h_dne : deriv (f.chartPullback x₀) ((chartAt ℂ x₀) x₀) ≠ 0 :=
    f.deriv_chartPullback_ne_zero_of_regular hnc hx₀
  exact (h_an.hasStrictDerivAt.hasStrictFDerivAt_equiv h_dne).toOpenPartialHomeomorph_coe

lemma isOpen_source_chartPullback_oph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    IsOpen (f.chartPullback_oph hnc hx₀).source :=
  (f.chartPullback_oph hnc hx₀).open_source

/-! ## Manifold-level `LocalSheetData` (chip 7) -/

/-- The manifold-level `OpenPartialHomeomorph X RiemannSphere`
representing `f.toRiemannSphere` locally at the regular point `x₀`.

Built as the trans-composition

  `c.trans ((φ.restrOpen c.target c.open_target).trans d.symm)`

(where `c = chartAt ℂ x₀`, `v₀ = f.toRiemannSphere x₀`, `d = chartAt ℂ v₀`,
`φ = chartPullback_oph`), further restricted to `f.toRiemannSphere ⁻¹'
d.source` so that the underlying function agrees with `f.toRiemannSphere`
on the source. -/
noncomputable def manifoldLocalOph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    OpenPartialHomeomorph X RiemannSphere :=
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀
  let v₀ : RiemannSphere := f.toRiemannSphere x₀
  let d : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ v₀
  let φ : OpenPartialHomeomorph ℂ ℂ := f.chartPullback_oph hnc hx₀
  let φ' : OpenPartialHomeomorph ℂ ℂ := φ.restrOpen c.target c.open_target
  let hf_cont : Continuous f.toRiemannSphere :=
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f).continuous
  let hpre_open : IsOpen (f.toRiemannSphere ⁻¹' d.source) :=
    hf_cont.isOpen_preimage _ d.open_source
  (c.trans (φ'.trans d.symm)).restrOpen
    (f.toRiemannSphere ⁻¹' d.source) hpre_open

/-- Auxiliary lemma: on the source of `manifoldLocalOph`, the underlying
function equals `f.toRiemannSphere`. -/
lemma manifoldLocalOph_apply
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet)
    {x : X} (hx : x ∈ (f.manifoldLocalOph hnc hx₀).source) :
    (f.manifoldLocalOph hnc hx₀ : X → RiemannSphere) x = f.toRiemannSphere x := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc_def
  set v₀ : RiemannSphere := f.toRiemannSphere x₀ with hv₀_def
  set d : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ v₀ with hd_def
  set φ : OpenPartialHomeomorph ℂ ℂ := f.chartPullback_oph hnc hx₀ with hφ_def
  set φ' : OpenPartialHomeomorph ℂ ℂ :=
    φ.restrOpen c.target c.open_target with hφ'_def
  have hf_cont : Continuous f.toRiemannSphere :=
    (JacobianChallenge.MeromorphicNonzero.toRiemannSphere_contMDiff f).continuous
  set hpre_open : IsOpen (f.toRiemannSphere ⁻¹' d.source) :=
    hf_cont.isOpen_preimage _ d.open_source with hpre_def
  -- Unfold the manifoldLocalOph source.
  have hx_src : x ∈ ((c.trans (φ'.trans d.symm))).source
      ∧ x ∈ f.toRiemannSphere ⁻¹' d.source := by
    rw [show (f.manifoldLocalOph hnc hx₀).source
        = ((c.trans (φ'.trans d.symm))).source ∩ f.toRiemannSphere ⁻¹' d.source
        from rfl] at hx
    exact hx
  obtain ⟨hx_trans, hx_fpre⟩ := hx_src
  -- Unpack the trans-source.
  rw [OpenPartialHomeomorph.trans_source] at hx_trans
  obtain ⟨hxc, hcx_inner⟩ := hx_trans
  rw [OpenPartialHomeomorph.trans_source] at hcx_inner
  obtain ⟨hcx_φ', hφ'cx_d⟩ := hcx_inner
  -- φ'.source = φ.source ∩ c.target.
  have hcx_φ : c x ∈ φ.source := hcx_φ'.1
  -- Underlying coe: (manifoldLocalOph) x = ((c.trans (φ'.trans d.symm))) x
  --                                       = d.symm (φ (c x)).
  show ((f.manifoldLocalOph hnc hx₀) : X → RiemannSphere) x = f.toRiemannSphere x
  rw [show ((f.manifoldLocalOph hnc hx₀) : X → RiemannSphere)
        = (c.trans (φ'.trans d.symm) : X → RiemannSphere) from rfl]
  rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply]
  -- Goal: d.symm (φ' (c x)) = f.toRiemannSphere x.
  -- φ' as function = φ (restrOpen doesn't change coe).
  have hφ'_coe : (φ' : ℂ → ℂ) = (φ : ℂ → ℂ) := rfl
  rw [show (d.symm : ℂ → RiemannSphere) ((φ' : ℂ → ℂ) (c x))
        = d.symm (φ (c x)) from by rw [hφ'_coe]]
  -- φ (c x) = f.chartPullback x₀ (c x) (by coe_chartPullback_oph).
  rw [show φ (c x) = f.chartPullback x₀ (c x)
        from by rw [← f.coe_chartPullback_oph hnc hx₀]]
  -- f.chartPullback x₀ (c x) = d (f.toRiemannSphere x).
  rw [show f.chartPullback x₀ (c x) = d (f.toRiemannSphere x) from by
    unfold chartPullback
    show ((chartAt ℂ v₀) ∘ f.toRiemannSphere ∘ (chartAt ℂ x₀).symm) (c x)
        = d (f.toRiemannSphere x)
    rw [Function.comp_apply, Function.comp_apply, c.left_inv hxc]]
  -- d.symm (d (f.toRiemannSphere x)) = f.toRiemannSphere x via d.left_inv.
  exact d.left_inv hx_fpre

/-- `x₀` lies in the source of `manifoldLocalOph`. -/
lemma mem_source_manifoldLocalOph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    x₀ ∈ (f.manifoldLocalOph hnc hx₀).source := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x₀ with hc_def
  set v₀ : RiemannSphere := f.toRiemannSphere x₀ with hv₀_def
  set d : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ v₀ with hd_def
  set φ : OpenPartialHomeomorph ℂ ℂ := f.chartPullback_oph hnc hx₀ with hφ_def
  set φ' : OpenPartialHomeomorph ℂ ℂ :=
    φ.restrOpen c.target c.open_target with hφ'_def
  have hx₀_c : x₀ ∈ c.source := mem_chart_source ℂ x₀
  have hv₀_d : v₀ ∈ d.source := mem_chart_source ℂ v₀
  have hcx₀_φ : c x₀ ∈ φ.source := f.mem_source_chartPullback_oph hnc hx₀
  have hcx₀_ct : c x₀ ∈ c.target := c.map_source hx₀_c
  -- φ (c x₀) = d v₀
  have hφcx₀ : φ (c x₀) = d v₀ := by
    rw [f.coe_chartPullback_oph hnc hx₀]
    unfold chartPullback
    show ((chartAt ℂ v₀) ∘ f.toRiemannSphere ∘ (chartAt ℂ x₀).symm) (c x₀)
        = d v₀
    rw [Function.comp_apply, Function.comp_apply, c.left_inv hx₀_c]
  have hφcx₀_dt : φ (c x₀) ∈ d.target := by
    rw [hφcx₀]; exact d.map_source hv₀_d
  -- Build the source membership.
  show x₀ ∈ (f.manifoldLocalOph hnc hx₀).source
  rw [show (f.manifoldLocalOph hnc hx₀).source
        = ((c.trans (φ'.trans d.symm))).source ∩ f.toRiemannSphere ⁻¹' d.source
        from rfl]
  refine ⟨?_, hv₀_d⟩
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨hx₀_c, ?_⟩
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨⟨hcx₀_φ, hcx₀_ct⟩, ?_⟩
  -- Need: φ' (c x₀) ∈ d.symm.source = d.target. φ' coe = φ coe.
  show (φ' : ℂ → ℂ) (c x₀) ∈ d.symm.source
  show (φ : ℂ → ℂ) (c x₀) ∈ d.symm.source
  rw [d.symm_source]
  exact hφcx₀_dt

/-- `v₀ := f.toRiemannSphere x₀` lies in the target of
`manifoldLocalOph`. -/
lemma mem_target_manifoldLocalOph
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    f.toRiemannSphere x₀ ∈ (f.manifoldLocalOph hnc hx₀).target := by
  have hx₀_src : x₀ ∈ (f.manifoldLocalOph hnc hx₀).source :=
    f.mem_source_manifoldLocalOph hnc hx₀
  have h := (f.manifoldLocalOph hnc hx₀).map_source hx₀_src
  -- This gives `(coe : X → RiemannSphere) x₀ ∈ target`. Rewrite coe via
  -- manifoldLocalOph_apply at x₀.
  rw [f.manifoldLocalOph_apply hnc hx₀ hx₀_src] at h
  exact h

/-! ## Assembly into `LocalSheetData` -/

/-- **Manifold-level `LocalSheetData` at every regular point.** -/
noncomputable def localSheetData_at_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx₀ : x₀ ∈ f.regularSet) :
    JacobianChallenge.LocalSheetData f.toRiemannSphere
      (f.toRiemannSphere x₀) x₀ where
  U := (f.manifoldLocalOph hnc hx₀).source
  U_open := (f.manifoldLocalOph hnc hx₀).open_source
  mem_U := f.mem_source_manifoldLocalOph hnc hx₀
  V := (f.manifoldLocalOph hnc hx₀).target
  V_open := (f.manifoldLocalOph hnc hx₀).open_target
  mem_V := f.mem_target_manifoldLocalOph hnc hx₀
  mapsTo := by
    intro x hx
    rw [← f.manifoldLocalOph_apply hnc hx₀ hx]
    exact (f.manifoldLocalOph hnc hx₀).map_source hx
  g := (f.manifoldLocalOph hnc hx₀).symm
  g_continuousOn := (f.manifoldLocalOph hnc hx₀).continuousOn_symm
  g_mapsTo := fun y hy => (f.manifoldLocalOph hnc hx₀).map_target hy
  leftInvOn := by
    intro x hx
    -- Goal: (manifoldLocalOph).symm (f.toRiemannSphere x) = x.
    -- Use manifoldLocalOph_apply to rewrite f.toRiemannSphere x as
    -- (manifoldLocalOph) x, then apply left_inv.
    rw [← f.manifoldLocalOph_apply hnc hx₀ hx]
    exact (f.manifoldLocalOph hnc hx₀).left_inv hx
  rightInvOn := by
    intro y hy
    -- Goal: f.toRiemannSphere ((manifoldLocalOph).symm y) = y.
    -- (manifoldLocalOph).symm y ∈ source via .symm.map_source applied to
    -- the symm's source = manifoldLocalOph.target.
    have hsy_src : (f.manifoldLocalOph hnc hx₀).symm y
        ∈ (f.manifoldLocalOph hnc hx₀).source := by
      have h := (f.manifoldLocalOph hnc hx₀).map_target hy
      exact h
    rw [← f.manifoldLocalOph_apply hnc hx₀ hsy_src]
    exact (f.manifoldLocalOph hnc hx₀).right_inv hy

/-! ## `IsLocalHomeomorphOn` on the regular set (chip 8) -/

/-- **`f.toRiemannSphere` is a local homeomorphism on `f.regularSet`.**

Direct consequence of `manifoldLocalOph` (chip 7) + `manifoldLocalOph_apply`
+ `IsLocalHomeomorphOn.mk` (which accepts the weaker
`Set.EqOn f e e.source` rather than global function equality). -/
theorem isLocalHomeomorphOn_toRiemannSphere
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    IsLocalHomeomorphOn f.toRiemannSphere f.regularSet := by
  refine IsLocalHomeomorphOn.mk f.toRiemannSphere f.regularSet ?_
  intro x hx
  refine ⟨f.manifoldLocalOph hnc hx, f.mem_source_manifoldLocalOph hnc hx, ?_⟩
  intro y hy
  exact (f.manifoldLocalOph_apply hnc hx hy).symm

/-- **`f.toRiemannSphere` is continuous at every regular point.**
Direct corollary of `IsLocalHomeomorphOn.continuousAt`. (Holds globally
via `MeromorphicNonzero.toRiemannSphere_contMDiff`, but this version is
exposed for direct downstream consumption.) -/
theorem continuousAt_toRiemannSphere_of_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x : X} (hx : x ∈ f.regularSet) :
    ContinuousAt f.toRiemannSphere x :=
  (f.isLocalHomeomorphOn_toRiemannSphere hnc).continuousAt hx

/-- **`f.toRiemannSphere` is open as a map on the regular set.** For
every `x ∈ f.regularSet` and every neighbourhood `U` of `x`, the image
`f.toRiemannSphere '' U` is a neighbourhood of `f.toRiemannSphere x`.
Direct corollary of `IsLocalHomeomorphOn.map_nhds_eq`. -/
theorem map_nhds_eq_of_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x : X} (hx : x ∈ f.regularSet) :
    (𝓝 x).map f.toRiemannSphere = 𝓝 (f.toRiemannSphere x) :=
  (f.isLocalHomeomorphOn_toRiemannSphere hnc).map_nhds_eq hx

end MeromorphicNonzero

end JacobianChallenge

end
