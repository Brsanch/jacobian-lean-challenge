/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option diagnostics.threshold 100

/-! # Smoothness of `localCoeff` on the chart target

For a holomorphic 1-form `om : HolomorphicOneForm X` on a complex
1-manifold `X` and base point `y : X`, this file extends
`HolomorphicOneForm.localCoeff_contMDiffAt_chart_image` (smoothness at
the single point `(chartAt ℂ y) y`) to *uniform smoothness* on the
entire chart target `(chartAt ℂ y).target`.

Concretely, `localCoeff om y` is `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on
`(chartAt ℂ y).target`, hence `AnalyticOn` there. This is the
regularity needed for Cauchy estimates over a closed disk inside the
chart target (the foundational analytic estimate for the
Forster/Montel/Riesz finite-dimensionality proof).

## Main results

* `HolomorphicOneForm.localCoeff_contMDiffOn` — `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
  (localCoeff om y) (chartAt ℂ y).target`.
* `HolomorphicOneForm.localCoeff_analyticOn` — `AnalyticOn ℂ
  (localCoeff om y) (chartAt ℂ y).target`.
* `HolomorphicOneForm.localCoeff_differentiableOn` —
  `DifferentiableOn ℂ (localCoeff om y) (chartAt ℂ y).target`.
* `HolomorphicOneForm.localCoeff_analyticAt` —
  `AnalyticAt ℂ (localCoeff om y) z` for any `z ∈ (chartAt ℂ y).target`.

## Implementation

The argument is the *cocycle transport* of the chart-coord
representative. The repo's existing canonical-chart bridge
(`cotangentSection_contMDiffAt_iff`) gives smoothness of
`coordChange (achart x) (achart y') x (om.toFun x)` at every
`y' ∈ X` (in the chart-`y'` frame). The cotangent bundle's
transition smoothness
(`cotangentBundleCore.isContMDiff (n := ω)`) gives smoothness of
the chart-to-chart transition
`coordChange (achart y') (achart y) ·` on the chart overlap
`(chartAt ℂ y').source ∩ (chartAt ℂ y).source`. Their pointwise
composition via `ContMDiffAt.clm_apply` is smooth at `y'`, and the
cocycle
`coordChange (achart y') (achart y) x ∘ coordChange (achart x)
(achart y') x = coordChange (achart x) (achart y) x` (valid on
triple-source intersections) identifies this composition with
the chart-`y`-frame representative pointwise on a neighbourhood of
`y'`. Hence the chart-`y`-frame representative is smooth on
`(chartAt ℂ y).source`. Composing with chart-symm gives smoothness
of `localCoeff om y` on `(chartAt ℂ y).target`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open Set

noncomputable section

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Helper: chart-coordinate representative of the section -/

/-- The chart-`y`-coordinate representative of `om : HolomorphicOneForm X`
as a function `X → ℂ →L[ℂ] ℂ`. -/
def chartCoordRepr (om : HolomorphicOneForm X) (y : X) : X → (ℂ →L[ℂ] ℂ) :=
  fun x =>
    (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ x) (achart ℂ y) x (om.toFun x)

/-- At the base point, the chart-coord repr equals the section value
(`coordChange` at same chart is the identity). -/
private lemma chartCoordRepr_self_apply (om : HolomorphicOneForm X) (y : X) :
    chartCoordRepr om y y = om.toFun y := by
  show (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
      (achart ℂ y) (achart ℂ y) y (om.toFun y) = om.toFun y
  apply cotangentBundleCore_coordChange_self
  show y ∈ (achart ℂ y).1.source
  rw [achart_val]
  exact mem_chart_source ℂ y

/-! ## Smoothness of the chart-coord repr at the base point

By the canonical-chart bridge — directly applicable since we are
in the chart of `y` itself. -/

/-- The chart-coord repr in chart `achart ℂ y'` is ContMDiffAt at `y'`. -/
private lemma chartCoordReprAtBase_contMDiffAt
    (om : HolomorphicOneForm X) (y' : X) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y') y' := by
  have h_om : ContMDiffAt 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (om.toFun x)) y' :=
    om.contMDiff.contMDiffAt
  rw [cotangentSection_contMDiffAt_iff (om.toFun)] at h_om
  exact h_om

/-! ## Cotangent bundle's transition smoothness

We need `coordChange j k x : (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)` smooth in
`x` on the chart overlap, at regularity ω. This follows from
`cotangentBundleCore.isContMDiff (n := ω)` since `IsManifold 𝓘(ℂ) ω X`
gives `IsManifold 𝓘(ℂ) (ω + 1) X` (because `ω + 1 = ω = ⊤` in
`WithTop ℕ∞`). -/

private lemma cotangentBundleCore_isContMDiff_omega :
    (cotangentBundleCore (𝓘(ℂ, ℂ)) X).IsContMDiff (𝓘(ℂ, ℂ)) ω := by
  haveI : IsManifold (𝓘(ℂ, ℂ)) (ω + 1) X := by
    have h_eq : (ω + 1 : WithTop ℕ∞) = ω := by
      change (⊤ + 1 : WithTop ℕ∞) = ⊤
      simp
    rw [h_eq]
    infer_instance
  exact cotangentBundleCore.isContMDiff (n := ω)

private lemma cotangentBundleCore_transition_contMDiffAt
    (y' y : X) (hy' : y' ∈ (chartAt ℂ y).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x) y' := by
  have h_isContMDiff := cotangentBundleCore_isContMDiff_omega (X := X)
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
      rw [achart_val]
      exact mem_chart_source ℂ y'
    · show y' ∈ (achart ℂ y).1.source
      rw [achart_val]
      exact hy'
  -- baseSets are open.
  have h_open : IsOpen ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y')
      ∩ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y)) := by
    refine IsOpen.inter ?_ ?_
    · show IsOpen (achart ℂ y').1.source
      rw [achart_val]
      exact (chartAt ℂ y').open_source
    · show IsOpen (achart ℂ y).1.source
      rw [achart_val]
      exact (chartAt ℂ y).open_source
  exact h_on.contMDiffAt (h_open.mem_nhds h_y'_inter)

/-! ## Cocycle identity on the chart overlap -/

/-- On the chart overlap `(chartAt y').source ∩ (chartAt y).source`,
the chart-coord repr `coordChange (achart x) (achart y) x v` equals
the composition through the achart-`y'` intermediate:
`(coordChange (achart y') (achart y) x) (coordChange (achart x)
(achart y') x v)`. -/
private lemma chartCoordRepr_cocycle_eventually
    (om : HolomorphicOneForm X) (y' y : X) (hy' : y' ∈ (chartAt ℂ y).source) :
    (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x (chartCoordRepr om y' x))
      =ᶠ[𝓝 y']
      (fun x : X => chartCoordRepr om y x) := by
  -- We need `(chartAt y').source ∩ (chartAt y).source` to be a nbhd of y'.
  have h_open : IsOpen ((chartAt ℂ y').source ∩ (chartAt ℂ y).source) :=
    (chartAt ℂ y').open_source.inter (chartAt ℂ y).open_source
  have h_mem : y' ∈ (chartAt ℂ y').source ∩ (chartAt ℂ y).source :=
    ⟨mem_chart_source ℂ y', hy'⟩
  filter_upwards [h_open.mem_nhds h_mem] with x hx
  -- For x in the overlap, the cocycle identity holds.
  -- Apply VectorBundleCore.coordChange_comp:
  -- (coordChange j k x) (coordChange i j x v) = coordChange i k x v
  -- with i = achart x, j = achart y', k = achart y.
  have h_x_inter :
      x ∈ (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ x) ∩
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y') ∩
        (cotangentBundleCore (𝓘(ℂ, ℂ)) X).baseSet (achart ℂ y) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show x ∈ (achart ℂ x).1.source
      rw [achart_val]
      exact mem_chart_source ℂ x
    · show x ∈ (achart ℂ y').1.source
      rw [achart_val]
      exact hx.1
    · show x ∈ (achart ℂ y).1.source
      rw [achart_val]
      exact hx.2
  show (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange (achart ℂ y') (achart ℂ y) x
        ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x) (achart ℂ y') x (om.toFun x))
      = (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
          (achart ℂ x) (achart ℂ y) x (om.toFun x)
  exact (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange_comp
    (achart ℂ x) (achart ℂ y') (achart ℂ y) x h_x_inter (om.toFun x)

/-! ## Chart-coord repr smooth on chart-`y` source -/

/-- The chart-coord repr `chartCoordRepr om y` is ContMDiffAt at every
point of `(chartAt ℂ y).source`. -/
theorem chartCoordRepr_contMDiffAt_in_chart_source
    (om : HolomorphicOneForm X) {y : X} {y' : X}
    (hy' : y' ∈ (chartAt ℂ y).source) :
    ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω (chartCoordRepr om y) y' := by
  -- Bridge at y' gives `chartCoordRepr om y'` is ContMDiffAt y'.
  have h_at_y' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y') y' :=
    chartCoordReprAtBase_contMDiffAt om y'
  -- Cotangent transition is smooth at y' on the chart overlap.
  have h_trans : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x) y' :=
    cotangentBundleCore_transition_contMDiffAt y' y hy'
  -- Apply CLM-applied-to-CLM (`ContMDiffAt.clm_apply`).
  have h_comp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun x : X => (cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ y') (achart ℂ y) x (chartCoordRepr om y' x)) y' :=
    h_trans.clm_apply h_at_y'
  -- Equate with `chartCoordRepr om y` via cocycle on a nbhd of y'.
  refine h_comp.congr_of_eventuallyEq ?_
  exact (chartCoordRepr_cocycle_eventually om y' y hy').symm

/-- The chart-coord repr `chartCoordRepr om y` is ContMDiffOn on
`(chartAt ℂ y).source`. -/
theorem chartCoordRepr_contMDiffOn
    (om : HolomorphicOneForm X) (y : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y) (chartAt ℂ y).source := by
  intro y' hy'
  exact (chartCoordRepr_contMDiffAt_in_chart_source om hy').contMDiffWithinAt

/-! ## Smoothness of `localCoeff` on the chart target -/

/-- Auxiliary: smoothness of `(· 1) : (ℂ →L[ℂ] ℂ) → ℂ`. -/
private lemma contMDiff_apply_one :
    ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (fun T : ℂ →L[ℂ] ℂ => T 1) := by
  have h : ContMDiff 𝓘(ℂ, ℂ →L[ℂ] ℂ) 𝓘(ℂ, ℂ) ω
      (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).contMDiff
  have h_eq : (fun T : ℂ →L[ℂ] ℂ => T 1)
      = (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)) := by
    funext T
    simp [ContinuousLinearMap.apply_apply]
  rw [h_eq]
  exact h

/-- The local coefficient `localCoeff om y` is
`ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on `(chartAt ℂ y).target`. -/
theorem localCoeff_contMDiffOn (om : HolomorphicOneForm X) (y : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (localCoeff om y) (chartAt ℂ y).target := by
  intro z hz
  -- Set y' := (chart y).symm z ∈ (chart y).source.
  set y' := (chartAt ℂ y).symm z with hy'_def
  have hy'_source : y' ∈ (chartAt ℂ y).source := by
    have hmaps : MapsTo (chartAt ℂ y).symm (chartAt ℂ y).target (chartAt ℂ y).source :=
      (chartAt ℂ y).symm.mapsTo
    exact hmaps hz
  -- chart-symm smooth at z.
  have h_symm_on : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ y).symm : ℂ → X) (chartAt ℂ y).target :=
    contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ω) (x := y)
  have h_symm_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      ((chartAt ℂ y).symm : ℂ → X) z :=
    h_symm_on.contMDiffAt ((chartAt ℂ y).open_target.mem_nhds hz)
  -- chart-coord repr at y' (= chart.symm z).
  have h_repr_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (chartCoordRepr om y) y' :=
    chartCoordRepr_contMDiffAt_in_chart_source om hy'_source
  -- Compose: chart-coord repr ∘ chart-symm at z.
  have h_comp_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun w : ℂ => chartCoordRepr om y ((chartAt ℂ y).symm w)) z := by
    have := h_repr_at.comp z h_symm_at
    simpa [Function.comp_def, hy'_def] using this
  -- Apply (· 1).
  have h_final_at : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun w : ℂ => (chartCoordRepr om y ((chartAt ℂ y).symm w)) 1) z :=
    contMDiff_apply_one.contMDiffAt.comp z h_comp_at
  -- Identify with `localCoeff om y` pointwise.
  have h_eq : (fun w : ℂ => (chartCoordRepr om y ((chartAt ℂ y).symm w)) 1)
      = localCoeff om y := by
    funext w
    show (chartCoordRepr om y ((chartAt ℂ y).symm w)) 1
        = localCoeff om y w
    show ((cotangentBundleCore (𝓘(ℂ, ℂ)) X).coordChange
        (achart ℂ ((chartAt ℂ y).symm w)) (achart ℂ y)
        ((chartAt ℂ y).symm w) (om.toFun ((chartAt ℂ y).symm w))) 1
        = localCoeff om y w
    rfl
  rw [h_eq] at h_final_at
  exact h_final_at.contMDiffWithinAt

/-! ## Analytic / differentiable corollaries -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The chart target is `UniqueDiffOn ℂ` (open in ℂ). -/
private lemma chartTarget_uniqueDiffOn (y : X) :
    UniqueDiffOn ℂ (chartAt ℂ y).target :=
  (chartAt ℂ y).open_target.uniqueDiffOn

/-- The local coefficient is `AnalyticOn ℂ` on the chart target. -/
theorem localCoeff_analyticOn (om : HolomorphicOneForm X) (y : X) :
    AnalyticOn ℂ (localCoeff om y) (chartAt ℂ y).target := by
  have h_contMDiff := localCoeff_contMDiffOn om y
  have h_contDiff : ContDiffOn ℂ ω (localCoeff om y) (chartAt ℂ y).target :=
    h_contMDiff.contDiffOn
  exact (contDiffOn_omega_iff_analyticOn (chartTarget_uniqueDiffOn y)).mp h_contDiff

/-- The local coefficient is `DifferentiableOn ℂ` on the chart target. -/
theorem localCoeff_differentiableOn (om : HolomorphicOneForm X) (y : X) :
    DifferentiableOn ℂ (localCoeff om y) (chartAt ℂ y).target :=
  (localCoeff_analyticOn om y).differentiableOn

/-- The local coefficient is `AnalyticAt ℂ` at every point of the chart
target. -/
theorem localCoeff_analyticAt (om : HolomorphicOneForm X) (y : X)
    {z : ℂ} (hz : z ∈ (chartAt ℂ y).target) :
    AnalyticAt ℂ (localCoeff om y) z :=
  (localCoeff_analyticOn om y).analyticAt
    ((chartAt ℂ y).open_target.mem_nhds hz)

/-- The local coefficient is `DifferentiableAt ℂ` at every point of the
chart target. -/
theorem localCoeff_differentiableAt (om : HolomorphicOneForm X) (y : X)
    {z : ℂ} (hz : z ∈ (chartAt ℂ y).target) :
    DifferentiableAt ℂ (localCoeff om y) z :=
  (localCoeff_analyticAt om y hz).differentiableAt

end HolomorphicOneForm

end
