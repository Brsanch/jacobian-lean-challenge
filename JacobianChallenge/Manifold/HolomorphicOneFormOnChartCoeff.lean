/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormOn
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Local coefficient of an `HolomorphicOneFormOn` at a base point

On-set analogue of `HolomorphicOneForm.localCoeff`
(`Manifold/HolomorphicOneFormChartCoeff.lean`). Given
`om : HolomorphicOneFormOn X s` and a base point `y : X`, the chart-`y`
local coefficient
`HolomorphicOneFormOn.localCoeff om y : ℂ → ℂ`
is the chart-frame coefficient of `dz` of `om`, with the same formula
as the global case.

The substantive content is the **chart-target on-set smoothness**:
on the open set `(chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source) ⊆
(chartAt ℂ y).target` — the chart image of the on-set portion of the
chart source — the local coefficient is `ContMDiffOn ω` /
`DifferentiableOn ℂ`.

The proof mirrors `HolomorphicOneFormChartCoeffOnTarget` with
`ContMDiffWithinAt _ _ _ s _` everywhere the global version has
`ContMDiffAt`. The cocycle transport (transition smoothness +
`ContMDiffWithinAt.clm_apply` + cocycle `congr_of_eventuallyEq` on
within-set neighbourhoods) is the same.

For the eventual `HolomorphicTraceExtension` globalize step, this is
applied with `y = v₀` a critical value of `f` and `s = f.regularValueSet`:
since the critical set is open-cofinite-discrete, the chart image of
`s ∩ (chartAt ℂ v₀).source` contains a punctured chart neighbourhood
of `(chartAt ℂ v₀) v₀`, and the local coefficient of
`f.fStarOmegaHolOn hnc α` is `DifferentiableOn ℂ` there.

## Main definitions

* `HolomorphicOneFormOn.localCoeff om y : ℂ → ℂ` — the chart-`y` local
  coefficient.

## Main results

* `HolomorphicOneFormOn.localCoeff_contMDiffOn_chartImage` —
  `ContMDiffOn ω` on the chart image of the on-set portion.
* `HolomorphicOneFormOn.localCoeff_differentiableOn_chartImage` —
  corollary `DifferentiableOn ℂ`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff
open Set Filter

noncomputable section

namespace HolomorphicOneFormOn

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] {s : Set X}

/-- The chart-`y` local coefficient of `om : HolomorphicOneFormOn X s`. -/
def localCoeff (om : HolomorphicOneFormOn X s) (y : X) : ℂ → ℂ :=
  fun z =>
    ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ y).symm z)) (achart ℂ y)
        ((chartAt ℂ y).symm z) (om.toFun ((chartAt ℂ y).symm z))) 1

/-! ## Chart-coord repr aux -/

/-- On-set chart-`y`-coordinate representative `X → ℂ →L[ℂ] ℂ`.
Same formula as `HolomorphicOneForm.chartCoordRepr`, just lifted from
the on-set form's `toFun`. -/
private def chartCoordRepr (om : HolomorphicOneFormOn X s) (y : X) :
    X → (ℂ →L[ℂ] ℂ) := fun x =>
  (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
    (achart ℂ x) (achart ℂ y) x (om.toFun x)

/-! ## Smoothness of `chartCoordRepr` at the base point — within-set s -/

/-- Within-set, at-base-point smoothness. At a point `y' ∈ s`, the
chart-`y'`-frame representative of `om` is `ContMDiffWithinAt ω` at
`y'` within `s` (via the cotangent-section bridge applied at `x₀ = y'`). -/
private lemma chartCoordReprAtBase_contMDiffWithinAt
    (om : HolomorphicOneFormOn X s) (y' : X) (hy' : y' ∈ s) :
    ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y') s y' := by
  have h_om : ContMDiffWithinAt 𝓘(ℂ, ℂ)
      ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (om.toFun x)) s y' :=
    om.contMDiffOn_section y' hy'
  rw [cotangentSection_contMDiffWithinAt_iff (I := 𝓘(ℂ, ℂ)) (n := ω)
    om.toFun] at h_om
  exact h_om

/-! ## Cotangent bundle transition smoothness — reused module-private
machinery. We re-derive the two cocycle pieces inline rather than
exposing the global file's `private` helpers. -/

private lemma cotangentBundleCore_isContMDiff_omega' :
    (cotangentBundleCore (𝓘(ℂ, ℂ)) X).IsContMDiff (𝓘(ℂ, ℂ)) ω := by
  haveI : IsManifold (𝓘(ℂ, ℂ)) (ω + 1) X := by
    have h_eq : (ω + 1 : WithTop ℕ∞) = ω := by
      change (⊤ + 1 : WithTop ℕ∞) = ⊤
      simp
    rw [h_eq]
    infer_instance
  exact cotangentBundleCore.isContMDiff (n := ω)

private lemma cotangentBundleCore_transition_contMDiffAt'
    (y' y : X) (hy' : y' ∈ (chartAt ℂ y).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x) y' := by
  have h_isContMDiff := cotangentBundleCore_isContMDiff_omega' (X := X)
  have h_on : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x)
      ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y') ∩
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y)) :=
    h_isContMDiff.contMDiffOn_coordChange (achart ℂ y') (achart ℂ y)
  have h_y'_inter : y' ∈ ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y')
      ∩ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y)) := by
    refine ⟨?_, ?_⟩
    · show y' ∈ (achart ℂ y').1.source
      rw [achart_val]; exact mem_chart_source ℂ y'
    · show y' ∈ (achart ℂ y).1.source
      rw [achart_val]; exact hy'
  have h_open : IsOpen ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y')
      ∩ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y)) := by
    refine IsOpen.inter ?_ ?_
    · show IsOpen (achart ℂ y').1.source
      rw [achart_val]; exact (chartAt ℂ y').open_source
    · show IsOpen (achart ℂ y).1.source
      rw [achart_val]; exact (chartAt ℂ y).open_source
  exact h_on.contMDiffAt (h_open.mem_nhds h_y'_inter)

/-! ## Cocycle identity on the chart overlap (toFun-parameterised) -/

private lemma chartCoordRepr_cocycle_eventually
    (om : HolomorphicOneFormOn X s) (y' y : X)
    (hy' : y' ∈ (chartAt ℂ y).source) :
    (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x (chartCoordRepr om y' x))
      =ᶠ[𝓝 y']
      (fun x : X => chartCoordRepr om y x) := by
  have h_open : IsOpen ((chartAt ℂ y').source ∩ (chartAt ℂ y).source) :=
    (chartAt ℂ y').open_source.inter (chartAt ℂ y).open_source
  have h_mem : y' ∈ (chartAt ℂ y').source ∩ (chartAt ℂ y).source :=
    ⟨mem_chart_source ℂ y', hy'⟩
  filter_upwards [h_open.mem_nhds h_mem] with x hx
  have h_x_inter :
      x ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ x) ∩
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y') ∩
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show x ∈ (achart ℂ x).1.source
      rw [achart_val]; exact mem_chart_source ℂ x
    · show x ∈ (achart ℂ y').1.source
      rw [achart_val]; exact hx.1
    · show x ∈ (achart ℂ y).1.source
      rw [achart_val]; exact hx.2
  show (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y') (achart ℂ y) x
        ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x) (achart ℂ y') x (om.toFun x))
      = (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x) (achart ℂ y) x (om.toFun x)
  exact (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ x) (achart ℂ y') (achart ℂ y) x h_x_inter (om.toFun x)

/-! ## Chart-coord repr smooth on `s ∩ (chartAt ℂ y).source` -/

/-- The chart-coord repr `chartCoordRepr om y` is `ContMDiffWithinAt ω`
at every point of `s ∩ (chartAt ℂ y).source`, within
`s ∩ (chartAt ℂ y).source`. -/
private theorem chartCoordRepr_contMDiffWithinAt_in_chart_source
    (om : HolomorphicOneFormOn X s) {y : X} {y' : X}
    (hy'_s : y' ∈ s) (hy'_source : y' ∈ (chartAt ℂ y).source) :
    ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y) (s ∩ (chartAt ℂ y).source) y' := by
  -- Bridge at y' gives chartCoordRepr om y' is ContMDiffWithinAt y' within s.
  have h_at_y'_s : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y') s y' :=
    chartCoordReprAtBase_contMDiffWithinAt om y' hy'_s
  -- Restrict to s ∩ chart.source.
  have h_at_y' : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y') (s ∩ (chartAt ℂ y).source) y' :=
    h_at_y'_s.mono Set.inter_subset_left
  -- Cotangent transition is ContMDiffAt y', → within any set.
  have h_trans_at : ContMDiffAt 𝓘(ℂ, ℂ)
      𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x) y' :=
    cotangentBundleCore_transition_contMDiffAt' y' y hy'_source
  have h_trans : ContMDiffWithinAt 𝓘(ℂ, ℂ)
      𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x) (s ∩ (chartAt ℂ y).source) y' :=
    h_trans_at.contMDiffWithinAt
  -- CLM-apply: composition within set.
  have h_comp : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x (chartCoordRepr om y' x))
      (s ∩ (chartAt ℂ y).source) y' :=
    h_trans.clm_apply h_at_y'
  -- Cocycle: equate with chartCoordRepr om y eventually within set.
  -- congr_of_eventuallyEq takes us from `cocycle-form` to `chartCoordRepr om y`.
  have h_eq_nhds : (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y') (achart ℂ y) x (chartCoordRepr om y' x))
      =ᶠ[𝓝 y'] (fun x : X => chartCoordRepr om y x) :=
    chartCoordRepr_cocycle_eventually om y' y hy'_source
  -- We need: chartCoordRepr om y =ᶠ[𝓝[s∩chart.source] y'] cocycle-form.
  have h_eq_nhdsWithin :
      (fun x : X => chartCoordRepr om y x)
        =ᶠ[𝓝[(s ∩ (chartAt ℂ y).source)] y']
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x (chartCoordRepr om y' x)) :=
    h_eq_nhds.symm.filter_mono nhdsWithin_le_nhds
  -- Point equality at y': cocycle identity at y' itself.
  have h_self : (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y') (achart ℂ y') y' (om.toFun y') = om.toFun y' := by
    apply (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_self (achart ℂ y') y'
    show y' ∈ (achart ℂ y').1.source
    rw [achart_val]; exact mem_chart_source ℂ y'
  have h_at_y_self_eq :
      chartCoordRepr om y y' =
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y') (achart ℂ y) y'
          (chartCoordRepr om y' y') := by
    show (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y') (achart ℂ y) y'
          (om.toFun y') =
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y') (achart ℂ y) y'
          ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y') (achart ℂ y') y'
            (om.toFun y'))
    rw [h_self]
  exact h_comp.congr_of_eventuallyEq h_eq_nhdsWithin h_at_y_self_eq

/-! ## Chart-target on-set smoothness -/

/-- **Main result.** On the chart image of `s ∩ (chartAt ℂ y).source`,
the local coefficient `om.localCoeff y` is `ContMDiffOn ω`. -/
theorem localCoeff_contMDiffOn_chartImage
    (om : HolomorphicOneFormOn X s) (y : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (om.localCoeff y)
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source)) := by
  -- Smoothness of (·1).
  have h_apply_one : ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (fun T : ℂ →L[ℂ] ℂ => T 1) := by
    have h : ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
        (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) :=
      (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiff
    have h_eq : (fun T : ℂ →L[ℂ] ℂ => T 1)
        = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) := by
      funext T; simp [ContinuousLinearMap.apply_apply]
    rw [h_eq]; exact h
  -- chart-symm smoothness on (chartAt y).target.
  have h_symm_on : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ y).symm : ℂ → X) (chartAt ℂ y).target :=
    contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := y)
  intro z hz
  obtain ⟨x, hx, hxz⟩ := hz
  -- hx : x ∈ s ∩ (chartAt ℂ y).source; hxz : (chartAt ℂ y) x = z.
  have h_chart_inv : (chartAt ℂ y).symm z = x := by
    rw [← hxz]; exact (chartAt ℂ y).left_inv hx.2
  have hz_in_target : z ∈ (chartAt ℂ y).target := by
    rw [← hxz]; exact (chartAt ℂ y).map_source hx.2
  have h_target_image_subset :
      (chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source) ⊆ (chartAt ℂ y).target := by
    rintro _ ⟨w, hw, rfl⟩; exact (chartAt ℂ y).map_source hw.2
  -- chart-symm at z within chart-image set.
  have h_symm_at : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ y).symm : ℂ → X)
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source)) z :=
    (h_symm_on z hz_in_target).mono h_target_image_subset
  -- chartCoordRepr om y at x within (s ∩ chart.source).
  have h_repr_at : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y) (s ∩ (chartAt ℂ y).source) x :=
    chartCoordRepr_contMDiffWithinAt_in_chart_source om hx.1 hx.2
  -- Transport via chart-symm.
  have h_repr_at_symm : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y) (s ∩ (chartAt ℂ y).source)
      ((chartAt ℂ y).symm z) := by
    rw [h_chart_inv]; exact h_repr_at
  -- chart-symm maps chart-image of (s ∩ chart.source) into s ∩ chart.source.
  have h_symm_maps : Set.MapsTo ((chartAt ℂ y).symm : ℂ → X)
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source))
      (s ∩ (chartAt ℂ y).source) := by
    rintro w ⟨x', hx', hx'w⟩
    rw [← hx'w, (chartAt ℂ y).left_inv hx'.2]
    exact hx'
  -- Compose: chartCoordRepr ∘ chart.symm at z within chart-image set.
  have h_comp_at : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun w : ℂ => chartCoordRepr om y ((chartAt ℂ y).symm w))
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source)) z := by
    have := h_repr_at_symm.comp z h_symm_at h_symm_maps
    simpa [Function.comp_def] using this
  -- Apply (·1) outside.
  have h_apply_at : ContMDiffAt 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (fun T : ℂ →L[ℂ] ℂ => T 1)
      (chartCoordRepr om y ((chartAt ℂ y).symm z)) := h_apply_one _
  have h_final : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun w : ℂ => (chartCoordRepr om y ((chartAt ℂ y).symm w)) 1)
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source)) z := by
    have := h_apply_at.comp_contMDiffWithinAt z h_comp_at
    simpa [Function.comp_def] using this
  -- Identify with om.localCoeff y pointwise.
  have h_eq : (fun w : ℂ => (chartCoordRepr om y ((chartAt ℂ y).symm w)) 1)
      = om.localCoeff y := by
    funext w; rfl
  rw [h_eq] at h_final
  exact h_final

/-! ## Differentiability corollary -/

/-- **DifferentiableOn corollary.** The local coefficient is
`DifferentiableOn ℂ` on the chart image of the on-set portion. This is
the form consumed by the `HolomorphicTraceExtension X` globalize step
together with the bounded-trace hypothesis. -/
theorem localCoeff_differentiableOn_chartImage
    (om : HolomorphicOneFormOn X s) (y : X) :
    DifferentiableOn ℂ (om.localCoeff y)
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source)) := by
  have h_contMDiff := localCoeff_contMDiffOn_chartImage om y
  have h_contDiff : ContDiffOn ℂ ω (om.localCoeff y)
      ((chartAt ℂ y) '' (s ∩ (chartAt ℂ y).source)) :=
    contMDiffOn_iff_contDiffOn.mp h_contMDiff
  exact h_contDiff.differentiableOn (by decide : (⊤ : WithTop ℕ∞) ≠ 0)

end HolomorphicOneFormOn

end
