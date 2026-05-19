/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorus
import JacobianChallenge.Manifold.PeriodLatticeComplexQuotientGeneric
import JacobianChallenge.Manifold.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option linter.unusedSectionVars false

/-! # Tangent-coord-change on `ℂ ⧸ L` is the identity

On the complex torus `T_L = ℂ ⧸ L`, every chart-change between two
atlas charts is, in a neighborhood of any point of the overlap source,
equal to a translation by a fixed lattice element `lam ∈ L`. The
Fréchet derivative of a translation `z ↦ z - lam` is the identity
ℂ-linear map `ContinuousLinearMap.id ℂ ℂ`.

Therefore the tangent coord-change
`tangentCoordChange 𝓘(ℂ, ℂ) y x z : ℂ →L[ℂ] ℂ` equals
`ContinuousLinearMap.id ℂ ℂ` for every `z` in the overlap of the
ext-chart-sources of `y` and `x`.

This is the core geometric fact underlying the **triviality of the
cotangent bundle on the complex torus** (precomposition with the
identity is the identity, so cotangent coord-change is also the
identity), which in turn unlocks the construction of the canonical
holomorphic 1-form `dz : HolomorphicOneForm (ℂ ⧸ L)` and hence the
Hodge basis at genus 1.

## What this file ships

* `ComplexTorus.fderiv_chart_transition_eq_id` — for any two
  base points `x y : ℂ ⧸ L` and any `z₀ ∈ ball x.out (r/2)` in the
  overlap, `fderiv ℂ ((chartAt y) ∘ (chartAt x).symm) z₀ =
  ContinuousLinearMap.id ℂ ℂ`.

* `ComplexTorus.tangentCoordChange_eq_id_on_overlap` — for any two
  base points `x y : ℂ ⧸ L` and any `z : ℂ ⧸ L` in the overlap of
  their ext-chart-sources, `tangentCoordChange 𝓘(ℂ, ℂ) x y z =
  ContinuousLinearMap.id ℂ ℂ`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Fréchet derivative of the translation map -/

/-- The Fréchet derivative of `z ↦ z - lam` on `ℂ` is the identity
ℂ-linear map. -/
private lemma fderiv_sub_const (lam : ℂ) (z : ℂ) :
    fderiv ℂ (fun x : ℂ => x - lam) z = ContinuousLinearMap.id ℂ ℂ := by
  have h : HasFDerivAt (fun x : ℂ => x - lam)
      (ContinuousLinearMap.id ℂ ℂ) z := by
    have h_id : HasFDerivAt (fun x : ℂ => x) (ContinuousLinearMap.id ℂ ℂ) z :=
      hasFDerivAt_id z
    have h_const : HasFDerivAt (fun _ : ℂ => lam) (0 : ℂ →L[ℂ] ℂ) z :=
      hasFDerivAt_const lam z
    have h_sub := h_id.sub h_const
    convert h_sub using 1
    ext v
    simp
  exact h.fderiv

/-! ## Chart-change on `ℂ ⧸ L` is locally a translation -/

/-- The composition `chartAt ℂ y ∘ (chartAt ℂ x).symm : ℂ → ℂ` equals
the trans-composition `(localChart L _ x.out).trans (localChart L _ y.out).symm`
as functions on the overlap (so they have the same local form `z ↦ z - lam`). -/
private lemma chart_change_eq_localChart_trans (x y : ℂ ⧸ L) :
    ((chartAt ℂ y : (ℂ ⧸ L) → ℂ) ∘ (chartAt ℂ x).symm)
      = ((localChart L (discRadius_separates L) x.out).trans
            (localChart L (discRadius_separates L) y.out).symm) := by
  rfl

/-- **Chart-change ℂ → ℂ on `ℂ ⧸ L` is locally a translation.** For
any two base points `x y : ℂ ⧸ L` and any `z₀` in the chart-change
source, the chart-change `chartAt ℂ y ∘ (chartAt ℂ x).symm` agrees, on
a neighborhood of `z₀`, with `z ↦ z - lam` for some `lam ∈ L`. -/
lemma chart_change_eventuallyEq_translation
    (x y : ℂ ⧸ L) {z₀ : ℂ}
    (hz₀ : z₀ ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    ∃ lam ∈ (L : Set ℂ),
      ((chartAt ℂ y : (ℂ ⧸ L) → ℂ) ∘ (chartAt ℂ x).symm)
          =ᶠ[nhds z₀] (fun z : ℂ => z - lam) := by
  -- Reinterpret the source: the chart-change here is the same as
  -- (localChart x.out).trans (localChart y.out).symm.
  have hz₀' : z₀ ∈ ((localChart L (discRadius_separates L) x.out).trans
      (localChart L (discRadius_separates L) y.out).symm).source := hz₀
  obtain ⟨lam, hlam_mem, h_eqOn⟩ :=
    transition_eventuallyEq_translation_generic L
      (discRadius_separates L) x.out y.out hz₀'
  refine ⟨lam, hlam_mem, ?_⟩
  rw [chart_change_eq_localChart_trans]
  exact h_eqOn

/-! ## fderiv of the chart-change on `ℂ ⧸ L` is the identity -/

/-- **Fréchet derivative of the chart-change is the identity.** For any
two base points `x y : ℂ ⧸ L` and any `z₀` in the chart-change source,
`fderiv ℂ (chartAt ℂ y ∘ (chartAt ℂ x).symm) z₀ = ContinuousLinearMap.id ℂ ℂ`.
Combines `chart_change_eventuallyEq_translation` with `fderiv_sub_const`
via `Filter.EventuallyEq.fderiv_eq`. -/
theorem fderiv_chart_change_eq_id
    (x y : ℂ ⧸ L) {z₀ : ℂ}
    (hz₀ : z₀ ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    fderiv ℂ ((chartAt ℂ y : (ℂ ⧸ L) → ℂ) ∘ (chartAt ℂ x).symm) z₀
      = ContinuousLinearMap.id ℂ ℂ := by
  obtain ⟨lam, _, h_eqOn⟩ :=
    chart_change_eventuallyEq_translation L x y hz₀
  rw [Filter.EventuallyEq.fderiv_eq h_eqOn]
  exact fderiv_sub_const lam z₀

/-! ## `tangentCoordChange 𝓘(ℂ,ℂ) x y z` is the identity on the chart overlap -/

/-- **`tangentCoordChange 𝓘(ℂ, ℂ) x y z = ContinuousLinearMap.id ℂ ℂ`** for
any `z : ℂ ⧸ L` in the overlap of the ext-chart-sources of `x` and `y`.

This is the core geometric triviality: chart-changes on `ℂ ⧸ L` are
translations, whose derivative is the identity. -/
theorem tangentCoordChange_eq_id_on_overlap
    (x y : ℂ ⧸ L) {z : ℂ ⧸ L}
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).source ∩
              (extChartAt 𝓘(ℂ, ℂ) y).source) :
    tangentCoordChange 𝓘(ℂ, ℂ) x y z = ContinuousLinearMap.id ℂ ℂ := by
  -- Unfold tangentCoordChange via `tangentBundleCore_coordChange_achart`.
  rw [tangentCoordChange_def]
  -- Goal: fderivWithin ℂ (extChartAt y ∘ (extChartAt x).symm) (range 𝓘(ℂ,ℂ)) (extChartAt x z) = id.
  -- range 𝓘(ℂ, ℂ) = univ, so fderivWithin = fderiv.
  have h_range : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) : Set ℂ) = Set.univ := by
    simp [ModelWithCorners.range_eq_univ]
  rw [h_range, fderivWithin_univ]
  -- For 𝓘(ℂ, ℂ), extChartAt = chartAt as functions.
  have h_ext_x : (extChartAt 𝓘(ℂ, ℂ) x : (ℂ ⧸ L) → ℂ) = (chartAt ℂ x : (ℂ ⧸ L) → ℂ) := by
    funext q
    rfl
  have h_ext_y : (extChartAt 𝓘(ℂ, ℂ) y : (ℂ ⧸ L) → ℂ) = (chartAt ℂ y : (ℂ ⧸ L) → ℂ) := by
    funext q
    rfl
  have h_ext_x_symm : ((extChartAt 𝓘(ℂ, ℂ) x).symm : ℂ → (ℂ ⧸ L))
      = ((chartAt ℂ x).symm : ℂ → (ℂ ⧸ L)) := by
    funext q
    rfl
  -- Rewrite extChartAt → chartAt.
  show fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) z) = ContinuousLinearMap.id ℂ ℂ
  rw [show ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm
        : ℂ → ℂ) = ((chartAt ℂ y : (ℂ ⧸ L) → ℂ) ∘ ((chartAt ℂ x).symm : ℂ → (ℂ ⧸ L)))
        from by rw [h_ext_y, h_ext_x_symm]]
  -- Apply fderiv_chart_change_eq_id.
  apply fderiv_chart_change_eq_id
  -- Now we need: (extChartAt x z) ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source.
  -- (chartAt x).symm.trans (chartAt y) has source = (chartAt x).symm⁻¹ (chartAt y).source ∩ ....
  -- Equivalently, (extChartAt x z) ∈ chartAt x z's image is in the trans source.
  -- We have z ∈ (extChartAt x).source ∩ (extChartAt y).source.
  -- (extChartAt x z) ∈ (chartAt x).target since z ∈ (chartAt x).source.
  -- And (chartAt x).symm ((chartAt x) z) = z ∈ (chartAt y).source, so (chartAt x z) ∈ (chartAt x).symm⁻¹ (chartAt y).source.
  obtain ⟨hzx, hzy⟩ := hz
  -- Coerce to chartAt source.
  rw [extChartAt_source] at hzx hzy
  -- Source of (chartAt x).symm.trans (chartAt y) is
  -- (chartAt x).target ∩ (chartAt x).symm ⁻¹' (chartAt y).source.
  have h_trans_src :
      ((chartAt ℂ x).symm.trans (chartAt ℂ y) :
          OpenPartialHomeomorph ℂ ℂ).source
        = (chartAt ℂ x).target ∩
            (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := by
    rfl
  rw [h_trans_src]
  refine ⟨?_, ?_⟩
  · -- (chartAt x) z ∈ (chartAt x).target.
    exact (chartAt ℂ x).map_source hzx
  · -- (chartAt x).symm ((extChartAt x) z) = z ∈ (chartAt y).source.
    rw [Set.mem_preimage]
    -- extChartAt 𝓘(ℂ,ℂ) x = chartAt ℂ x as functions.
    change (chartAt ℂ x).symm ((chartAt ℂ x) z) ∈ (chartAt ℂ y).source
    rw [(chartAt ℂ x).left_inv hzx]
    exact hzy

/-! ## Cotangent coord-change on `ℂ ⧸ L` is the identity -/

/-- **`cotangentBundleCore.coordChange (achart x) (achart y) z ξ = ξ`**
on the chart overlap. Combines `cotangentBundleCore_coordChange_apply`
(which writes cotangent coordChange in terms of tangent coordChange via
postcomposition) with `tangentCoordChange_eq_id_on_overlap`. -/
theorem cotangentBundleCore_coordChange_eq_id_on_overlap
    (x y : ℂ ⧸ L) {z : ℂ ⧸ L}
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).source ∩
              (extChartAt 𝓘(ℂ, ℂ) y).source)
    (ξ : ℂ →L[ℂ] ℂ) :
    (cotangentBundleCore (𝓘(ℂ, ℂ)) (ℂ ⧸ L)).coordChange
        (achart ℂ x) (achart ℂ y) z ξ = ξ := by
  -- Unfold via the explicit formula for cotangentBundleCore.coordChange.
  -- (cotangentBundleCore I M).coordChange i j x ξ = ξ.comp (tangent coordChange j i x).
  rw [_root_.cotangentBundleCore_coordChange_apply]
  -- Goal: ξ.comp ((tangentBundleCore _).coordChange (achart y) (achart x) z) = ξ.
  -- We have tangentCoordChange y x z = id (since z in y∩x overlap = x∩y overlap).
  have h_tan : tangentCoordChange 𝓘(ℂ, ℂ) y x z = ContinuousLinearMap.id ℂ ℂ :=
    tangentCoordChange_eq_id_on_overlap L y x ⟨hz.2, hz.1⟩
  have h_tan' : (tangentBundleCore 𝓘(ℂ, ℂ) (ℂ ⧸ L)).coordChange
      (achart ℂ y) (achart ℂ x) z = ContinuousLinearMap.id ℂ ℂ := h_tan
  rw [h_tan']
  ext v
  simp

end ComplexTorus

end JacobianChallenge

end
