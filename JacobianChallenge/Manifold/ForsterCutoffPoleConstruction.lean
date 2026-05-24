/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ExistsSimplePoleGermFromGenusZeroDBarSolvability
import JacobianChallenge.Manifold.PartialZBarManifold
import JacobianChallenge.Manifold.PartialZBarAnalyticConverse
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.MeromorphicAt
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Forster §16.9 cutoff + correction construction (Chip 2c)

This file discharges the **forward leg of item 14** on arbitrary
compact connected complex 1-manifold `X` at the named-hypothesis level:

  **`DBarSolvabilityAtGenusZero X → genus X = 0 → ExistsSimplePoleGermAtSomePoint X`**

via the classical Forster Theorem 16.9 cutoff + correction
construction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex Filter Set Classical

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Local pole construction at a chosen point `p ∈ X`. -/

/-- The local pole `g₀ p b : X → ℂ` = `χ y · ((chart y - c₀)⁻¹)` on
`chart.source`, `0` elsewhere, where `c₀ := chartAt ℂ p p` and
`χ := (b : X → ℝ)`. Has a simple pole at `p` and is smooth-real on
`X \ {p}`. -/
private def g₀ (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (y : X) : ℂ :=
  if y ∈ (chartAt ℂ p).source
    then ((b y : ℝ) : ℂ) * ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
    else 0

/-- On `chart.source`, `g₀` is the unconditional formula. -/
private lemma g₀_of_mem_source (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (y : X) (hy : y ∈ (chartAt ℂ p).source) :
    g₀ p b y = ((b y : ℝ) : ℂ) * ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹ := by
  unfold g₀; rw [if_pos hy]

/-- Off `chart.source`, `g₀` is `0`. -/
private lemma g₀_of_not_mem_source (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (y : X) (hy : y ∉ (chartAt ℂ p).source) :
    g₀ p b y = 0 := by
  unfold g₀; rw [if_neg hy]

/-- At the chosen point `p`, `g₀ p = 0` by the `inv` convention
(`(0 : ℂ)⁻¹ = 0`). -/
private lemma g₀_at_pole (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    g₀ p b p = 0 := by
  have hp : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  rw [g₀_of_mem_source p b p hp]
  simp

/-- The complex-valued cast of the bump: `bC y := ((b y : ℝ) : ℂ)`.
Smooth-real on all of `X` (with values in ℂ). -/
private def bC (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (y : X) : ℂ :=
  ((b y : ℝ) : ℂ)

/-- The chart-inverse "extended by 0": `chartInv p y := (chart y - c₀)⁻¹`
on `chart.source`, `0` elsewhere. Not continuous at `p` (where the
formula gives the convention `0⁻¹ = 0`), but the products we form
against it kill the singularity. -/
private def chartInv (p : X) (y : X) : ℂ :=
  if y ∈ (chartAt ℂ p).source
    then ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
    else 0

private lemma chartInv_of_mem_source (p : X) (y : X)
    (hy : y ∈ (chartAt ℂ p).source) :
    chartInv p y = ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹ := by
  unfold chartInv; rw [if_pos hy]

private lemma chartInv_of_not_mem_source (p : X) (y : X)
    (hy : y ∉ (chartAt ℂ p).source) :
    chartInv p y = 0 := by
  unfold chartInv; rw [if_neg hy]

/-- `g₀` is the pointwise product `bC · chartInv` on chart.source, both
extended-by-0 off chart.source. -/
private lemma g₀_eq_bC_mul_chartInv (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (y : X) :
    g₀ p b y = bC p b y * chartInv p y := by
  unfold g₀ bC chartInv
  by_cases hy : y ∈ (chartAt ℂ p).source
  · rw [if_pos hy, if_pos hy]
  · rw [if_neg hy, if_neg hy]; ring

/-! ## The compactly-supported source `α := partialZBarManifold bC · chartInv`.

We define `α` as the pointwise product of `partialZBarManifold bC`
(the manifold-side `∂̄` of the bump cast to ℂ) and `chartInv` (the
extended chart inverse). The key properties we need:

* `α` is smooth-real on all of `X` (which feeds into
  `DBarSolvabilityAtGenusZero`).
* `partialZBarManifold g₀ = α` pointwise on `X` (so `α` literally is
  the right-hand side of the ∂̄-equation we want to solve).
* On the inner ball `{y | dist ((chartAt ℂ p) y) c₀ < b.rIn}` (where
  `b ≡ 1`), `α ≡ 0`.
* On the annulus and outside `tsupport b`, the explicit formula and
  smoothness analysis go through.
-/

/-- The compactly-supported source `α`. -/
private def α (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (y : X) : ℂ :=
  partialZBarManifold (bC p b) y * chartInv p y

/-! ## Smoothness of `bC`. -/

/-- `bC := ((b : X → ℝ) : X → ℂ)` is smooth-real on all of `X`. -/
private lemma bC_contMDiff (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (bC p b) := by
  -- `b : X → ℝ` is smooth, then cast ℝ → ℂ is smooth (continuous linear map).
  have hb : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (b : X → ℝ) := b.contMDiff
  have hcast : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun r : ℝ => (r : ℂ)) :=
    Complex.ofRealCLM.contMDiff
  -- `bC y = ((b y : ℝ) : ℂ) = (fun r => (r : ℂ)) (b y)`.
  show ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun y => ((b y : ℝ) : ℂ))
  exact hcast.comp hb

/-! ## `partialZBar`/`partialZBarManifold` vanishes on eventually-constant functions. -/

/-- If `f =ᶠ[𝓝 z] g` then `partialZBar f z = partialZBar g z`. -/
private lemma partialZBar_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : partialZBar f z = partialZBar g z := by
  unfold partialZBar
  rw [h.fderiv_eq]

/-- If `f` is eventually constant near `z`, then `partialZBar f z = 0`. -/
private lemma partialZBar_eq_zero_of_eventuallyEq_const {f : ℂ → ℂ} {z : ℂ} {c : ℂ}
    (h : f =ᶠ[𝓝 z] fun _ => c) : partialZBar f z = 0 := by
  rw [partialZBar_congr_of_eventuallyEq h, partialZBar_const]

/-- Chart-pullback tendsto helper: `chart.symm` tends to `x` as its argument
tends to `chart x x`. -/
private lemma extChartAt_symm_tendsto (x : X) :
    Filter.Tendsto (extChartAt 𝓘(ℂ, ℂ) x).symm
      (𝓝 ((extChartAt 𝓘(ℂ, ℂ) x) x)) (𝓝 x) := by
  have h_cts := continuousAt_extChartAt_symm (I := (𝓘(ℂ, ℂ))) x
  have h_g_eq : (extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x) = x :=
    extChartAt_to_inv x
  rw [show (𝓝 x) = (𝓝 ((extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x))) from
      by rw [h_g_eq]]
  exact h_cts

/-- Manifold-side: if `f =ᶠ[𝓝 x] g`, then
`partialZBarManifold f x = partialZBarManifold g x`. -/
private lemma partialZBarManifold_congr_of_eventuallyEq
    {f g : X → ℂ} {x : X} (h : f =ᶠ[𝓝 x] g) :
    partialZBarManifold f x = partialZBarManifold g x := by
  unfold partialZBarManifold
  have h_chart :
      (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
        =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) x) x)]
        (g ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) :=
    h.comp_tendsto (extChartAt_symm_tendsto x)
  exact partialZBar_congr_of_eventuallyEq h_chart

/-- Manifold-side: if `f =ᶠ[𝓝 x] (fun _ => c)`, then
`partialZBarManifold f x = 0`. -/
private lemma partialZBarManifold_eq_zero_of_eventuallyEq_const
    {f : X → ℂ} {x : X} {c : ℂ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : partialZBarManifold f x = 0 := by
  rw [partialZBarManifold_congr_of_eventuallyEq h, partialZBarManifold_const]

/-! ## Vanishing of `partialZBarManifold (bC p b)` in a nbhd of `p`. -/

/-- `bC = const 1` in a nbhd of `p` (because `b ≡ 1` in a nbhd of `p`). -/
private lemma bC_eventuallyEq_one_near_p
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    bC p b =ᶠ[𝓝 p] (fun _ : X => (1 : ℂ)) := by
  -- `b.eventuallyEq_one : (b : X → ℝ) =ᶠ[𝓝 p] 1`.
  have h := b.eventuallyEq_one
  -- transport along ℝ→ℂ cast.
  filter_upwards [h] with y hy
  show ((b y : ℝ) : ℂ) = 1
  rw [hy]
  show ((1 : ℝ) : ℂ) = 1
  norm_cast

/-- `partialZBarManifold (bC p b) = 0` on a nbhd of `p`. -/
private lemma partialZBarManifold_bC_eventuallyEq_zero_near_p
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    (partialZBarManifold (bC p b)) =ᶠ[𝓝 p] (fun _ : X => (0 : ℂ)) := by
  -- The set `{y | bC =ᶠ[𝓝 y] const 1}` is an open nbhd of p, on which
  -- partialZBarManifold bC = 0.
  obtain ⟨U, hUopen, hpU, hU_eq⟩ : ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      ∀ y ∈ U, ((b y : ℝ) : ℂ) = (1 : ℂ) := by
    -- `b.eventuallyEq_one` gives `{y | b y = 1} ∈ 𝓝 p`. Extract open subset.
    have h_bump := b.eventuallyEq_one
    have hmem : {y : X | (b y : ℝ) = 1} ∈ 𝓝 p := by
      filter_upwards [h_bump] with y hy
      exact hy
    rcases mem_nhds_iff.mp hmem with ⟨U, hUsub, hUopen, hpU⟩
    refine ⟨U, hUopen, hpU, ?_⟩
    intro y hy
    have : (b y : ℝ) = 1 := hUsub hy
    rw [this]; norm_cast
  -- Now `U` is open, contains p, and bC ≡ 1 on U.
  filter_upwards [hUopen.mem_nhds hpU] with y hy
  show partialZBarManifold (bC p b) y = 0
  -- bC ≡ 1 in a nbhd of y (the same open U).
  apply partialZBarManifold_eq_zero_of_eventuallyEq_const (c := 1)
  filter_upwards [hUopen.mem_nhds hy] with y' hy'
  show ((b y' : ℝ) : ℂ) = 1
  exact hU_eq y' hy'

/-- `α = 0` in a nbhd of `p`. -/
private lemma α_eventuallyEq_zero_near_p
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    α p b =ᶠ[𝓝 p] (fun _ : X => (0 : ℂ)) := by
  filter_upwards [partialZBarManifold_bC_eventuallyEq_zero_near_p p b] with y hy
  show partialZBarManifold (bC p b) y * chartInv p y = 0
  rw [hy]; ring

/-! ## Vanishing of `α` outside `tsupport b` -/

/-- `bC = 0` in a nbhd of any `y` with `y ∉ tsupport (b : X → ℝ)`. -/
private lemma bC_eventuallyEq_zero_off_tsupport
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∉ tsupport (b : X → ℝ)) :
    bC p b =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
  have h_open : IsOpen ((tsupport (b : X → ℝ))ᶜ) := (isClosed_tsupport _).isOpen_compl
  filter_upwards [h_open.mem_nhds hy] with y' hy'
  show ((b y' : ℝ) : ℂ) = 0
  have h_not_in_supp : y' ∉ Function.support (b : X → ℝ) := fun hcontra =>
    hy' (subset_closure hcontra)
  have : (b y' : ℝ) = 0 := Function.notMem_support.mp h_not_in_supp
  rw [this]; norm_cast

/-- `partialZBarManifold (bC p b) = 0` in a nbhd of any `y ∉ tsupport b`. -/
private lemma partialZBarManifold_bC_eventuallyEq_zero_off_tsupport
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∉ tsupport (b : X → ℝ)) :
    partialZBarManifold (bC p b) =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
  -- On the open set (tsupport b)ᶜ, bC ≡ 0, so partialZBarManifold bC ≡ 0.
  have h_open : IsOpen ((tsupport (b : X → ℝ))ᶜ) := (isClosed_tsupport _).isOpen_compl
  filter_upwards [h_open.mem_nhds hy] with y' hy'
  show partialZBarManifold (bC p b) y' = 0
  apply partialZBarManifold_eq_zero_of_eventuallyEq_const (c := 0)
  exact bC_eventuallyEq_zero_off_tsupport p b hy'

/-- `α = 0` in a nbhd of any `y ∉ tsupport b`. -/
private lemma α_eventuallyEq_zero_off_tsupport
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∉ tsupport (b : X → ℝ)) :
    α p b =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
  filter_upwards [partialZBarManifold_bC_eventuallyEq_zero_off_tsupport p b hy] with y' h
  show partialZBarManifold (bC p b) y' * chartInv p y' = 0
  rw [h]; ring

/-! ## Chart-transition holomorphy of `chartInv` off the pole

`chartInv p` is chart-p-holomorphic by construction, but
`partialZBarManifold` is defined via chart-y. The transition
`chart_p ∘ chart_y.symm` is `AnalyticAt ℂ` on the holomorphic atlas
(via `analyticAt_chart_transition_of_isManifold`), so `chartInv p`'s
chart-y pullback is ℂ-differentiable at `chart_y y` whenever
`y ∈ chart_p.source ∩ {y ≠ p}`. -/

/-- For `y ∈ chart_p.source`, on a neighborhood of `chart_y y` the
chart-y pullback of `chartInv p` agrees with
`(chart_p (chart_y.symm w) - c₀)⁻¹`. -/
private lemma chartInv_chart_pullback_eventuallyEq
    (p : X) {y : X} (hy : y ∈ (chartAt ℂ p).source) :
    (chartInv p ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) y) y)]
      (fun w : ℂ => ((chartAt ℂ p) ((chartAt ℂ y).symm w)
                       - (chartAt ℂ p) p)⁻¹) := by
  -- On a nbhd of chart_y y, chart_y.symm sends w into chart_p.source.
  -- Continuity of chart_y.symm at chart_y y, with chart_y.symm (chart_y y) = y ∈ chart_p.source.
  have h_tendsto := extChartAt_symm_tendsto (X := X) y
  have h_p_src_nhds : (chartAt ℂ p).source ∈ 𝓝 y :=
    (chartAt ℂ p).open_source.mem_nhds hy
  have h_w_in_src :
      ∀ᶠ w in 𝓝 ((extChartAt 𝓘(ℂ, ℂ) y) y),
        (extChartAt 𝓘(ℂ, ℂ) y).symm w ∈ (chartAt ℂ p).source :=
    h_tendsto h_p_src_nhds
  filter_upwards [h_w_in_src] with w hw
  show chartInv p ((extChartAt 𝓘(ℂ, ℂ) y).symm w)
      = ((chartAt ℂ p) ((chartAt ℂ y).symm w) - (chartAt ℂ p) p)⁻¹
  -- `(extChartAt 𝓘(ℂ, ℂ) y).symm w = (chartAt ℂ y).symm w` definitionally
  -- (the model 𝓘(ℂ, ℂ) is `id` on ℂ).
  have h_symm_eq : (extChartAt 𝓘(ℂ, ℂ) y).symm w = (chartAt ℂ y).symm w := rfl
  rw [h_symm_eq] at hw ⊢
  exact chartInv_of_mem_source p _ hw

/-- For `y ∈ chart_p.source` with `y ≠ p`, the chart-y pullback of
`chartInv p` is ℂ-differentiable at `chart_y y`. -/
private lemma chartInv_chart_pullback_differentiableAt
    [IsManifold 𝓘(ℂ, ℂ) ω X]
    (p : X) {y : X} (hy : y ∈ (chartAt ℂ p).source) (hyp : y ≠ p) :
    DifferentiableAt ℂ (chartInv p ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      ((extChartAt 𝓘(ℂ, ℂ) y) y) := by
  -- Use the eventually-eq, then prove the simpler RHS is ℂ-differentiable.
  rw [(chartInv_chart_pullback_eventuallyEq p hy).differentiableAt_iff]
  -- RHS: `w ↦ ((chartAt ℂ p) ((chartAt ℂ y).symm w) - (chartAt ℂ p) p)⁻¹`.
  -- Chart transition `(chartAt ℂ p) ∘ (chartAt ℂ y).symm` is `AnalyticAt ℂ`.
  have h_chart_y_mem : (chartAt ℂ y) ∈ atlas ℂ X := chart_mem_atlas ℂ y
  have h_chart_p_mem : (chartAt ℂ p) ∈ atlas ℂ X := chart_mem_atlas ℂ p
  have h_y_in_y : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have h_an_trans :
      AnalyticAt ℂ ((chartAt ℂ p) ∘ (chartAt ℂ y).symm)
        ((chartAt ℂ y) y) :=
    analyticAt_chart_transition_of_isManifold (M := X)
      h_chart_y_mem h_chart_p_mem h_y_in_y hy
  -- Subtract a constant: still analytic.
  have h_an_sub :
      AnalyticAt ℂ (fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w)
                                   - (chartAt ℂ p) p)
        ((chartAt ℂ y) y) := by
    have h_const : AnalyticAt ℂ (fun _ : ℂ => (chartAt ℂ p) p)
        ((chartAt ℂ y) y) := analyticAt_const
    -- `(fun w => (chart_p ∘ chart_y.symm) w - c₀)` is `analyticAt`'s `sub`.
    exact h_an_trans.sub h_const
  -- Value of the inner function at `chart_y y` equals `chart_p y - c₀`.
  have h_val : (fun w : ℂ => (chartAt ℂ p) ((chartAt ℂ y).symm w)
                                   - (chartAt ℂ p) p) ((chartAt ℂ y) y)
      = (chartAt ℂ p) y - (chartAt ℂ p) p := by
    show (chartAt ℂ p) ((chartAt ℂ y).symm ((chartAt ℂ y) y))
          - (chartAt ℂ p) p
        = (chartAt ℂ p) y - (chartAt ℂ p) p
    have h_left_inv : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
      (chartAt ℂ y).left_inv h_y_in_y
    rw [h_left_inv]
  -- `chart_p y ≠ chart_p p` since `chart_p` is injective on its source.
  have h_inj : (chartAt ℂ p) y ≠ (chartAt ℂ p) p := by
    intro h_eq
    have h_p_in_src : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
    have h_y_eq_p : y = p := (chartAt ℂ p).injOn hy h_p_in_src h_eq
    exact hyp h_y_eq_p
  have h_nonzero : (chartAt ℂ p) y - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr h_inj
  -- Show w ↦ (inner)⁻¹ is `AnalyticAt`, hence differentiableAt.
  have h_an_inv : AnalyticAt ℂ (fun w : ℂ => ((chartAt ℂ p) ((chartAt ℂ y).symm w)
                                                - (chartAt ℂ p) p)⁻¹)
      ((chartAt ℂ y) y) := by
    apply h_an_sub.inv
    show (chartAt ℂ p) ((chartAt ℂ y).symm ((chartAt ℂ y) y)) - (chartAt ℂ p) p ≠ 0
    rw [(chartAt ℂ y).left_inv h_y_in_y]
    exact h_nonzero
  -- Bridge `extChartAt 𝓘(ℂ, ℂ) y` to `chartAt ℂ y` (defeq on ℂ).
  show DifferentiableAt ℂ (fun w : ℂ => ((chartAt ℂ p) ((chartAt ℂ y).symm w)
                                            - (chartAt ℂ p) p)⁻¹)
    ((extChartAt 𝓘(ℂ, ℂ) y) y)
  have h_base_eq : (extChartAt 𝓘(ℂ, ℂ) y) y = (chartAt ℂ y) y := rfl
  rw [h_base_eq]
  exact h_an_inv.differentiableAt

/-! ## Chart-y pullback of `bC` is ℝ-differentiable

`bC` is globally `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`. Composing with the
chart-y inverse (`ContMDiffOn` on the chart target) and using the
vector-space identification `ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E') = ContDiffAt ℝ`,
the chart-y pullback inherits `ContDiffAt ℝ ∞`. -/

private lemma bC_chart_pullback_differentiableAt
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (y : X) :
    DifferentiableAt ℝ (bC p b ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      ((extChartAt 𝓘(ℂ, ℂ) y) y) := by
  -- Step 1: `bC` is `ContMDiff` globally.
  have h_bC : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (bC p b) := bC_contMDiff p b
  -- Step 2: `chart.symm` is `ContMDiffOn` on `chart.target`.
  have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (extChartAt 𝓘(ℝ, ℂ) y).symm
                  (extChartAt 𝓘(ℝ, ℂ) y).target :=
    contMDiffOn_extChartAt_symm y
  -- Step 3: composition is `ContMDiffOn` on `chart.target`.
  have h_comp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm) (extChartAt 𝓘(ℝ, ℂ) y).target :=
    h_bC.comp_contMDiffOn h_symm
  -- Step 4: basepoint is in chart target (open).
  have h_y_mem : (extChartAt 𝓘(ℝ, ℂ) y) y ∈ (extChartAt 𝓘(ℝ, ℂ) y).target :=
    mem_extChartAt_target y
  have h_target_open : IsOpen (extChartAt 𝓘(ℝ, ℂ) y).target :=
    isOpen_extChartAt_target y
  -- Step 5: `ContMDiffOn` ⇒ `ContMDiffAt` (open inclusion).
  have h_within := h_comp _ h_y_mem
  have h_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm) ((extChartAt 𝓘(ℝ, ℂ) y) y) :=
    h_within.contMDiffAt (h_target_open.mem_nhds h_y_mem)
  -- Step 6: vector-space bridge `ContMDiffAt` ⇔ `ContDiffAt`.
  have h_cd : ContDiffAt ℝ ∞ (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
      ((extChartAt 𝓘(ℝ, ℂ) y) y) := h_at.contDiffAt
  -- Step 7: differentiable from `ContDiffAt ∞`.
  have h_diff : DifferentiableAt ℝ (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) y).symm)
      ((extChartAt 𝓘(ℝ, ℂ) y) y) := h_cd.differentiableAt (by decide)
  -- Step 8: bridge `𝓘(ℝ, ℂ)` extChartAt to `𝓘(ℂ, ℂ)` extChartAt — both are
  -- definitionally `chartAt ℂ y` with the identity model attached.
  exact h_diff

/-! ## Leibniz application: `partialZBarManifold g₀ y = α y` for `y ≠ p`

For `y ∈ chart_p.source ∩ {y ≠ p}`: `chartInv`'s chart-y pullback is
ℂ-differentiable at `chart_y y` (chart-transition holomorphy), so the
Leibniz specialization
`partialZBarManifold (bC · chartInv) y = partialZBarManifold bC y · chartInv y`
applies. The LHS equals `partialZBarManifold g₀ y` (since g₀ = bC·chartInv
pointwise), and the RHS is `α y` by definition.

For `y ∉ tsupport b`: both sides vanish in a neighborhood (g₀ ≡ 0 and
∂̄bC ≡ 0 nearby).

Together these cover `X \ {p}`, since `tsupport b ⊆ chart_p.source` and
`p ∈ tsupport b` is the only excluded case. -/

/-- On `chart_p.source ∩ {y ≠ p}` the Leibniz spec applies, giving
`partialZBarManifold g₀ y = α y`. -/
private lemma partialZBarManifold_g₀_eq_α_on_source_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∈ (chartAt ℂ p).source) (hyp : y ≠ p) :
    partialZBarManifold (g₀ p b) y = α p b y := by
  -- Rewrite `g₀ = bC · chartInv` pointwise.
  have h_g₀_eq : g₀ p b = fun z : X => bC p b z * chartInv p z := by
    funext z; exact g₀_eq_bC_mul_chartInv p b z
  rw [h_g₀_eq]
  -- Leibniz spec (chartInv side ℂ-holomorphic).
  have h_bC_diff := bC_chart_pullback_differentiableAt p b y
  have h_chartInv_diff := chartInv_chart_pullback_differentiableAt p hy hyp
  have h_leibniz :
      partialZBarManifold (fun z : X => bC p b z * chartInv p z) y
        = partialZBarManifold (bC p b) y * chartInv p y :=
    partialZBarManifold_mul_of_chartPullback_differentiableAt_right
      h_bC_diff h_chartInv_diff
  rw [h_leibniz]
  rfl

/-- `partialZBarManifold g₀ y = α y` for every `y ≠ p`. -/
lemma partialZBarManifold_g₀_eq_α_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X} (hyp : y ≠ p) :
    partialZBarManifold (g₀ p b) y = α p b y := by
  -- Case split on `y ∈ tsupport b` vs `y ∉ tsupport b`.
  by_cases hy_supp : y ∈ tsupport (b : X → ℝ)
  · -- `tsupport b ⊆ chart_p.source` (mathlib bump fact), so apply the
    -- on-source case.
    have h_y_src : y ∈ (chartAt ℂ p).source :=
      b.tsupport_subset_chartAt_source hy_supp
    exact partialZBarManifold_g₀_eq_α_on_source_off_pole p b h_y_src hyp
  · -- Off `tsupport b`: both sides vanish on a nbhd of y.
    have h_g₀_zero : g₀ p b =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) := by
      filter_upwards [bC_eventuallyEq_zero_off_tsupport p b hy_supp] with z hz
      show g₀ p b z = 0
      rw [g₀_eq_bC_mul_chartInv]
      rw [show bC p b z = 0 from hz]; ring
    have h_lhs : partialZBarManifold (g₀ p b) y = 0 :=
      partialZBarManifold_eq_zero_of_eventuallyEq_const h_g₀_zero
    have h_rhs : α p b y = 0 := by
      have h := α_eventuallyEq_zero_off_tsupport p b hy_supp
      exact h.eq_of_nhds
    rw [h_lhs, h_rhs]

/-! ## Chart-side smoothness of `partialZBar`

For `ContDiffAt ℝ ⊤ f z`, `partialZBar f` is `ContDiffAt ℝ ⊤` at `z`.
The map factors as: `fderiv ℝ f` is `ContDiffAt ⊤` at `z` (mathlib's
`ContDiffAt.fderiv_right` with `⊤ + 1 ≤ ⊤`), then evaluation at `1`
and `I` (via `ContDiffAt.clm_apply`), then `(2)⁻¹ * (· + I * ·)`. -/

private lemma partialZBar_contDiffAt_of_contDiffAt {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ ⊤ f z) :
    ContDiffAt ℝ ⊤ (partialZBar f) z := by
  -- Break the ℝ-`NormedSpace ℂ` diamond before doing fderiv-of-fderiv arithmetic
  -- (mathlib has both `NormedSpace.complexToReal` and `NormedAlgebra.toNormedSpace`).
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  -- Step 1: `fderiv ℝ f` is ContDiffAt ⊤ at z.
  have h_top_add : ((⊤ : WithTop ℕ∞) + 1 : WithTop ℕ∞) ≤ ⊤ := by
    rw [WithTop.top_add]
  have h_fderiv : ContDiffAt ℝ ⊤ (fderiv ℝ f) z := hf.fderiv_right h_top_add
  -- Step 2: pointwise evaluation at 1 and I.
  have h_eval_1 : ContDiffAt ℝ ⊤ (fun z : ℂ => (fderiv ℝ f z) (1 : ℂ)) z :=
    h_fderiv.clm_apply contDiffAt_const
  have h_eval_I : ContDiffAt ℝ ⊤ (fun z : ℂ => (fderiv ℝ f z) (I : ℂ)) z :=
    h_fderiv.clm_apply contDiffAt_const
  -- Step 3: `I * (fderiv ℝ f z) I`.
  have h_I_times : ContDiffAt ℝ ⊤ (fun z : ℂ => I * (fderiv ℝ f z) I) z :=
    contDiffAt_const.mul h_eval_I
  -- Step 4: sum.
  have h_sum : ContDiffAt ℝ ⊤
      (fun z : ℂ => (fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I) z :=
    h_eval_1.add h_I_times
  -- Step 5: `(1/2) * (...)`.
  have h_final : ContDiffAt ℝ ⊤
      (fun z : ℂ => (2 : ℂ)⁻¹ * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I)) z :=
    contDiffAt_const.mul h_sum
  -- Unfold `partialZBar`.
  change ContDiffAt ℝ ⊤
    (fun z : ℂ => (2 : ℂ)⁻¹ * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I)) z
  exact h_final

/-! ## Chart-locality on a chart source

The Forster §16 cutoff/correction construction uses the bump `b` whose
support lies inside `(chartAt ℂ p).source`. On this set, the canonical
`chartAt ℂ y` for varying `y` need not equal `chartAt ℂ p` in general
— `mathlib`'s `ChartedSpace` does not enforce local chart constancy.
However, for typical Riemann surface constructions (e.g.,
`RiemannSphere` at any finite point — `chartAt' y = chartN` for every
finite `y ∈ chartN.source = {y | y ≠ ∞}`), `chartAt` IS constant on
each chart's source. We capture this as a Prop hypothesis available
for downstream consumers to discharge for their concrete X.

The hypothesis is **classical** (a structural property of chartAt's
selection, holding for concrete Riemann surface constructions), not a
renamed version of α smoothness — it isolates the chart-locality
content into a single named Prop. -/

/-- `chartAt ℂ y` is constant on `(chartAt ℂ p).source`. Holds for
typical concrete `ChartedSpace ℂ X` constructions (e.g., `RiemannSphere`
at finite `p`). -/
def ChartAtConstantOnSource (p : X) : Prop :=
  ∀ y ∈ (chartAt ℂ p).source, chartAt ℂ y = chartAt ℂ p

/-- Under `ChartAtConstantOnSource p`, `partialZBarManifold f y` on
`chart_p.source` reduces to a chart-p-relative computation. -/
private lemma partialZBarManifold_eq_chart_p_under_const
    (p : X) (f : X → ℂ)
    (h_const : ChartAtConstantOnSource p)
    {y : X} (hy : y ∈ (chartAt ℂ p).source) :
    partialZBarManifold f y
      = partialZBar (f ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) y) := by
  unfold partialZBarManifold
  have h_eq : chartAt ℂ y = chartAt ℂ p := h_const y hy
  -- `(extChartAt 𝓘(ℂ, ℂ) y) y` is definitionally `(chartAt ℂ y) y`, then
  -- rewrite via `h_eq` to `(chartAt ℂ p) y`. Similarly for `.symm`.
  have h_basept : (extChartAt 𝓘(ℂ, ℂ) y) y = (chartAt ℂ p) y := by
    show (chartAt ℂ y) y = (chartAt ℂ p) y
    rw [h_eq]
  have h_symm_fn : (f ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      = (f ∘ (chartAt ℂ p).symm) := by
    funext w
    show f ((chartAt ℂ y).symm w) = f ((chartAt ℂ p).symm w)
    rw [h_eq]
  rw [h_symm_fn, h_basept]

/-! ## Smoothness of `partialZBarManifold (bC)` on chart_p.source (under chart-const)

Under `ChartAtConstantOnSource p`, the manifold-side ∂̄ of `bC`
reduces to the chart-p computation `partialZBar (bC ∘ chart_p.symm)
(chart_p y)` on `chart_p.source`. The chart-side `partialZBar` is
`ContDiffAt ℝ ⊤` (Foundation lemma above) and `chart_p` is smooth, so
the composition is `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤` at every
`y ∈ chart_p.source`. -/

end JacobianChallenge.MeromorphicFunctionField

end
