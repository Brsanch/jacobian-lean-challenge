/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HurwitzManifold
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.MeromorphicAt

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Transport of `mmeromorphicOrderAt` through a `HolomorphicEquiv`

A biholomorphism `e : HolomorphicEquiv X Y` (analytic in both directions)
transports `MMeromorphicAt` and preserves `mmeromorphicOrderAt`: for any
`f : Y → ℂ` and `x : X`,

  `mmeromorphicOrderAt 𝓘(ℂ,ℂ) (f ∘ e) x = mmeromorphicOrderAt 𝓘(ℂ,ℂ) f (e x)`.

The chart-pullback identity is the key step: writing
`φ := chartAt ℂ (e x) ∘ e ∘ (chartAt ℂ x).symm`, mathlib's
`meromorphicOrderAt_comp_of_deriv_ne_zero` (with `φ` analytic and
`deriv φ ((chartAt ℂ x) x) ≠ 0`) gives

  `meromorphicOrderAt ((f ∘ chartAt ℂ (e x).symm) ∘ φ) ((chartAt ℂ x) x)
     = meromorphicOrderAt (f ∘ chartAt ℂ (e x).symm) (φ ((chartAt ℂ x) x))`.

The LHS agrees on a chart-source neighborhood with the chart pullback of
`f ∘ e` (via `chart.symm ∘ chart = id`), and the RHS basepoint
`φ ((chartAt ℂ x) x)` reduces to `(chartAt ℂ (e x)) (e x)`. Both sides
are exactly `mmeromorphicOrderAt`'s definitional unfoldings.

## Inputs reused

* `ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback`
  — `e` `ContMDiff` `ω` gives the chart-transition analytic.
* `ContMDiff.deriv_chart_pullback_ne_zero_of_injective`
  — `e` `ContMDiff` `ω` plus `Injective e.toFun` gives the derivative
  is non-zero (`HolomorphicEquiv` is bijective).
* `meromorphicOrderAt_comp_of_deriv_ne_zero` — mathlib comp formula.

## Contents

* `HolomorphicEquiv.chartTransition_analyticAt` — chart transition is
  analytic.
* `HolomorphicEquiv.chartTransition_deriv_ne_zero` — chart transition's
  derivative is non-zero.
* `MMeromorphicAt.holomorphicEquiv_comp_iff` — `MMeromorphicAt (f ∘ e) x
  ↔ MMeromorphicAt f (e x)`.
* `mmeromorphicOrderAt_holomorphicEquiv_comp` — the order equality.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge

universe u v

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]
variable {Y : Type v}
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-! ## Chart-transition analyticity + non-zero derivative -/

/-- The chart transition `(chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm`
of a `HolomorphicEquiv` is `AnalyticAt ℂ` at `(chartAt ℂ x) x`. -/
lemma HolomorphicEquiv.chartTransition_analyticAt
    (e : HolomorphicEquiv X Y) (x : X) :
    AnalyticAt ℂ ((chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) := by
  -- `e` is `ContMDiff ω`, so the chart pullback is analytic.
  have h_cmd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.toEquiv : X → Y) :=
    e.contMDiff_toFun
  exact JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
    h_cmd x

/-- The chart transition's derivative is non-zero (since a
`HolomorphicEquiv` is bijective, hence injective). -/
lemma HolomorphicEquiv.chartTransition_deriv_ne_zero
    (e : HolomorphicEquiv X Y) (x : X) :
    deriv ((chartAt ℂ (e x)) ∘ e ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0 := by
  have h_cmd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.toEquiv : X → Y) :=
    e.contMDiff_toFun
  have h_inj : Function.Injective (e.toEquiv : X → Y) :=
    e.toEquiv.injective
  exact JacobianChallenge.Manifold.ContMDiff.deriv_chart_pullback_ne_zero_of_injective
    h_cmd h_inj x

/-! ## Chart-pullback eventual equality -/

/-- On a chart-source neighborhood of `(chartAt ℂ x) x`, the
double-chart-pulled-back form `(f ∘ chartAt ℂ (e x).symm) ∘ φ` agrees
with `(f ∘ e) ∘ (chartAt ℂ x).symm`, where `φ = chartAt ℂ (e x) ∘ e ∘
(chartAt ℂ x).symm`. -/
lemma HolomorphicEquiv.chart_pullback_eventuallyEq
    (e : HolomorphicEquiv X Y) (f : Y → ℂ) (x : X) :
    ((f ∘ (chartAt ℂ (e x)).symm) ∘
        ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm))
      =ᶠ[𝓝 ((chartAt ℂ x) x)]
    ((f ∘ (e.toEquiv : X → Y)) ∘ (chartAt ℂ x).symm) := by
  -- The preimage `chartAt ℂ x.symm ⁻¹' (chartAt ℂ x.source)` includes a nbhd
  -- of (chartAt ℂ x) x; on this nbhd, (chart.symm) lands in chart.source.
  -- Then `chart_y.symm ∘ chart_y = id` on the y-chart source (where
  -- y = e (chart_x.symm z) lies on the relevant nbhd).
  -- We extract the open nbhd of (chartAt ℂ x) x as
  --   `chartAt ℂ x.target ∩ (chartAt ℂ x.symm) ⁻¹' ((e.toEquiv : X → Y) ⁻¹' chartAt ℂ (e x).source)`.
  have h_chart_x_open : IsOpen (chartAt ℂ x).target :=
    (chartAt ℂ x).open_target
  have h_chartx_x : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  -- `chart.symm` is continuous on chart.target, so the preimage of the
  -- chart-y-source open set is open in chart.target near (chart x) x.
  have h_sym_cont :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
    (chartAt ℂ x).continuousAt_symm h_chartx_x
  -- e is continuous, so the y-chart-source preimage is open.
  have h_e_cont : ContinuousAt (e.toEquiv : X → Y) x := by
    have h_cmd : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (e.toEquiv : X → Y) :=
      e.contMDiff_toFun
    exact (h_cmd x).continuousAt
  -- The set V := chartAt ℂ x.target ∩ (chartAt ℂ x.symm) ⁻¹' (e ⁻¹' chartAt ℂ (e x).source)
  -- is open and contains (chartAt ℂ x) x.
  have h_y_src_nhds :
      (chartAt ℂ (e x)).source ∈ 𝓝 (e x) :=
    (chartAt ℂ (e x)).open_source.mem_nhds (mem_chart_source ℂ (e x))
  have h_pre1 :
      (e.toEquiv : X → Y) ⁻¹' (chartAt ℂ (e x)).source ∈ 𝓝 x :=
    h_e_cont.preimage_mem_nhds h_y_src_nhds
  have h_pre2 :
      (chartAt ℂ x).symm ⁻¹' ((e.toEquiv : X → Y) ⁻¹' (chartAt ℂ (e x)).source)
        ∈ 𝓝 ((chartAt ℂ x) x) := by
    apply h_sym_cont.preimage_mem_nhds
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact h_pre1
  -- Now build the EvEq on a nbhd of (chartAt ℂ x) x using the open V.
  filter_upwards [h_pre2,
    h_chart_x_open.mem_nhds h_chartx_x] with z hz_pre hz_tgt
  -- Goal: (f ∘ chart_y.symm) (chart_y (e (chart_x.symm z))) = f (e (chart_x.symm z)).
  -- Need: e (chart_x.symm z) ∈ chart_y.source so chart_y.symm ∘ chart_y is id.
  have hy_in_src : (e.toEquiv : X → Y) ((chartAt ℂ x).symm z)
      ∈ (chartAt ℂ (e x)).source := hz_pre
  show (f ∘ (chartAt ℂ (e x)).symm)
      ((chartAt ℂ (e x)) ((e.toEquiv : X → Y) ((chartAt ℂ x).symm z))) =
    (f ∘ (e.toEquiv : X → Y)) ((chartAt ℂ x).symm z)
  show f ((chartAt ℂ (e x)).symm
      ((chartAt ℂ (e x)) ((e.toEquiv : X → Y) ((chartAt ℂ x).symm z)))) =
    f ((e.toEquiv : X → Y) ((chartAt ℂ x).symm z))
  rw [(chartAt ℂ (e x)).left_inv hy_in_src]

/-! ## Order transport -/

/-- **`mmeromorphicOrderAt (f ∘ e) x = mmeromorphicOrderAt f (e x)`** for
any `e : HolomorphicEquiv X Y` and `f : Y → ℂ`. -/
theorem mmeromorphicOrderAt_holomorphicEquiv_comp
    (e : HolomorphicEquiv X Y) (f : Y → ℂ) (x : X) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) (f ∘ (e.toEquiv : X → Y)) x
      = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f (e x) := by
  -- Unfold both sides to chart-pulled-back form.
  show meromorphicOrderAt ((f ∘ (e.toEquiv : X → Y)) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x)
      = meromorphicOrderAt (f ∘ (chartAt ℂ (e x)).symm)
          ((chartAt ℂ (e x)) (e x))
  -- Set up the chart transition `φ` and its analyticity/deriv-non-zero.
  have h_an : AnalyticAt ℂ
      ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) :=
    HolomorphicEquiv.chartTransition_analyticAt e x
  have h_deriv : deriv
      ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0 :=
    HolomorphicEquiv.chartTransition_deriv_ne_zero e x
  -- Compose with `f ∘ chart_y.symm` and use mathlib's order-of-comp.
  have h_comp_order :
      meromorphicOrderAt
        ((f ∘ (chartAt ℂ (e x)).symm) ∘
          ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm))
        ((chartAt ℂ x) x)
      = meromorphicOrderAt (f ∘ (chartAt ℂ (e x)).symm)
          (((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
              ((chartAt ℂ x) x)) :=
    meromorphicOrderAt_comp_of_deriv_ne_zero h_an h_deriv
  -- The basepoint `φ ((chartAt ℂ x) x)` reduces to `(chartAt ℂ (e x)) (e x)`.
  have h_basepoint :
      ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x)
        = (chartAt ℂ (e x)) (e x) := by
    show (chartAt ℂ (e x)) ((e.toEquiv : X → Y) ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
      = (chartAt ℂ (e x)) (e x)
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    rfl
  rw [h_basepoint] at h_comp_order
  -- The LHS of h_comp_order agrees on a nbhd of (chartAt ℂ x) x with
  -- (f ∘ e) ∘ chart_x.symm via `chart_y.symm ∘ chart_y = id`.
  have h_ev_eq :
      ((f ∘ (chartAt ℂ (e x)).symm) ∘
          ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm))
        =ᶠ[𝓝 ((chartAt ℂ x) x)]
      ((f ∘ (e.toEquiv : X → Y)) ∘ (chartAt ℂ x).symm) :=
    HolomorphicEquiv.chart_pullback_eventuallyEq e f x
  -- Drop to punctured nbhd for the meromorphicOrderAt_congr.
  have h_ev_eq_punctured :
      ((f ∘ (chartAt ℂ (e x)).symm) ∘
          ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm))
        =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      ((f ∘ (e.toEquiv : X → Y)) ∘ (chartAt ℂ x).symm) :=
    h_ev_eq.filter_mono nhdsWithin_le_nhds
  rw [meromorphicOrderAt_congr h_ev_eq_punctured.symm]
  exact h_comp_order

/-! ## `MMeromorphicAt` transport -/

/-- **`MMeromorphicAt (f ∘ e) x ↔ MMeromorphicAt f (e x)`.** Composition
with a `HolomorphicEquiv` preserves manifold-meromorphic-at structure. -/
theorem MMeromorphicAt.holomorphicEquiv_comp_iff
    (e : HolomorphicEquiv X Y) (f : Y → ℂ) (x : X) :
    MMeromorphicAt 𝓘(ℂ, ℂ) (f ∘ (e.toEquiv : X → Y)) x
      ↔ MMeromorphicAt 𝓘(ℂ, ℂ) f (e x) := by
  show MeromorphicAt ((f ∘ (e.toEquiv : X → Y)) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x)
      ↔ MeromorphicAt (f ∘ (chartAt ℂ (e x)).symm)
          ((chartAt ℂ (e x)) (e x))
  have h_an : AnalyticAt ℂ
      ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) :=
    HolomorphicEquiv.chartTransition_analyticAt e x
  have h_deriv : deriv
      ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0 :=
    HolomorphicEquiv.chartTransition_deriv_ne_zero e x
  have h_basepoint :
      ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x)
        = (chartAt ℂ (e x)) (e x) := by
    show (chartAt ℂ (e x)) ((e.toEquiv : X → Y) ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
      = (chartAt ℂ (e x)) (e x)
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    rfl
  have h_ev_eq :
      ((f ∘ (chartAt ℂ (e x)).symm) ∘
          ((chartAt ℂ (e x)) ∘ (e.toEquiv : X → Y) ∘ (chartAt ℂ x).symm))
        =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      ((f ∘ (e.toEquiv : X → Y)) ∘ (chartAt ℂ x).symm) :=
    (HolomorphicEquiv.chart_pullback_eventuallyEq e f x).filter_mono nhdsWithin_le_nhds
  rw [← h_basepoint, ← meromorphicAt_comp_iff_of_deriv_ne_zero h_an h_deriv]
  exact ⟨fun h => h.congr h_ev_eq.symm,
         fun h => h.congr h_ev_eq⟩

end JacobianChallenge

end
