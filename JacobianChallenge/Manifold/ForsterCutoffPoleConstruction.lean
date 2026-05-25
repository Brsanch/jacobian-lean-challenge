/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ExistsSimplePoleGermFromGenusZeroDBarSolvability
import JacobianChallenge.Manifold.PartialZBarManifold
import JacobianChallenge.Manifold.PartialZBarManifoldChartPullbackVanish
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

private lemma partialZBar_contDiffAt_of_contDiffAt
    {n : WithTop ℕ∞} (hn : n + 1 ≤ n)
    {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ n f z) :
    ContDiffAt ℝ n (partialZBar f) z := by
  -- Break the ℝ-`NormedSpace ℂ` diamond before doing fderiv-of-fderiv arithmetic
  -- (mathlib has both `NormedSpace.complexToReal` and `NormedAlgebra.toNormedSpace`).
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  -- Step 1: `fderiv ℝ f` is ContDiffAt n at z.
  have h_fderiv : ContDiffAt ℝ n (fderiv ℝ f) z := hf.fderiv_right hn
  -- Step 2: pointwise evaluation at 1 and I.
  have h_eval_1 : ContDiffAt ℝ n (fun z : ℂ => (fderiv ℝ f z) (1 : ℂ)) z :=
    h_fderiv.clm_apply contDiffAt_const
  have h_eval_I : ContDiffAt ℝ n (fun z : ℂ => (fderiv ℝ f z) (I : ℂ)) z :=
    h_fderiv.clm_apply contDiffAt_const
  -- Step 3: `I * (fderiv ℝ f z) I`.
  have h_I_times : ContDiffAt ℝ n (fun z : ℂ => I * (fderiv ℝ f z) I) z :=
    contDiffAt_const.mul h_eval_I
  -- Step 4: sum.
  have h_sum : ContDiffAt ℝ n
      (fun z : ℂ => (fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I) z :=
    h_eval_1.add h_I_times
  -- Step 5: `(1/2) * (...)`.
  have h_final : ContDiffAt ℝ n
      (fun z : ℂ => (2 : ℂ)⁻¹ * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I)) z :=
    contDiffAt_const.mul h_sum
  -- Unfold `partialZBar`.
  change ContDiffAt ℝ n
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
`ContDiffAt ℝ ∞` (Foundation lemma above) and `chart_p` is smooth, so
the composition is `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` at every
`y ∈ chart_p.source`. -/

/-- Helper: `∞ + 1 ≤ ∞` in `WithTop ℕ∞` (∞ here is `(⊤ : ℕ∞)` lifted). -/
private lemma infty_add_one_le_infty :
    ((∞ : WithTop ℕ∞) + 1 : WithTop ℕ∞) ≤ ∞ := by
  show ((((⊤ : ℕ∞) : WithTop ℕ∞)) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  rw [show (1 : WithTop ℕ∞) = ((1 : ℕ∞) : WithTop ℕ∞) from rfl, ← WithTop.coe_add]
  exact le_refl _

/-- The chart-y pullback `bC ∘ chart_p.symm : ℂ → ℂ` is `ContDiffOn ℝ ∞`
on `chart_p.target`. Composes `bC_contMDiff` (global `ContMDiff ∞`) with
mathlib's `contMDiffOn_extChartAt_symm`, then dualizes via the
vector-space `ContMDiffOn ↔ ContDiffOn`. -/
private lemma bC_chart_p_symm_contDiffOn
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    ContDiffOn ℝ ∞ (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
      (extChartAt 𝓘(ℝ, ℂ) p).target := by
  have h_bC : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (bC p b) := bC_contMDiff p b
  have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (extChartAt 𝓘(ℝ, ℂ) p).symm
                  (extChartAt 𝓘(ℝ, ℂ) p).target :=
    contMDiffOn_extChartAt_symm p
  have h_comp : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) (extChartAt 𝓘(ℝ, ℂ) p).target :=
    h_bC.comp_contMDiffOn h_symm
  exact contMDiffOn_iff_contDiffOn.mp h_comp

/-- `partialZBar (bC ∘ chart_p.symm)` is `ContDiffOn ℝ ∞` on
`chart_p.target`. Applies the foundation `partialZBar_contDiffAt_of_contDiffAt`
pointwise on the open chart target. -/
private lemma partialZBar_bC_chart_p_symm_contDiffOn
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    ContDiffOn ℝ ∞ (partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm))
      (extChartAt 𝓘(ℝ, ℂ) p).target := by
  intro z hz
  have h_target_open : IsOpen (extChartAt 𝓘(ℝ, ℂ) p).target :=
    isOpen_extChartAt_target p
  have h_cd_within := (bC_chart_p_symm_contDiffOn p b) z hz
  -- Upgrade `ContDiffWithinAt` to `ContDiffAt` (open inclusion).
  have h_cd_at : ContDiffAt ℝ ∞ (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z :=
    h_cd_within.contDiffAt (h_target_open.mem_nhds hz)
  -- Apply chart-side `partialZBar` smoothness with `n = ∞`.
  have h_pZ : ContDiffAt ℝ ∞ (partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)) z :=
    partialZBar_contDiffAt_of_contDiffAt infty_add_one_le_infty h_cd_at
  exact h_pZ.contDiffWithinAt

/-- Under `ChartAtConstantOnSource p`, `partialZBarManifold (bC p b)` is
`ContMDiffOn ∞` on `(chartAt ℂ p).source`. -/
lemma partialZBarManifold_bC_contMDiffOn_under_const
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (partialZBarManifold (bC p b)) (chartAt ℂ p).source := by
  intro y hy
  -- On chart_p.source the chart-p reduction lemma applies.
  -- Build the chart-p representative `g := partialZBar (bC ∘ chart_p.symm) ∘ chart_p`.
  -- Show `g` is ContMDiffWithinAt at y in chart_p.source via composition.
  -- Then conclude `partialZBarManifold (bC) y = g y` and lift.
  have h_chart : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (chartAt ℂ p) (chartAt ℂ p).source := contMDiffOn_chart
  have h_pZ : ContDiffOn ℝ ∞
      (partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm))
      (extChartAt 𝓘(ℝ, ℂ) p).target := partialZBar_bC_chart_p_symm_contDiffOn p b
  have h_pZ_mdiff : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm))
      (extChartAt 𝓘(ℝ, ℂ) p).target := contMDiffOn_iff_contDiffOn.mpr h_pZ
  -- chart_p maps chart_p.source into (extChartAt 𝓘(ℝ, ℂ) p).target.
  -- Use `(extChartAt I p).map_source` and the defeq `(extChartAt I p) x = (chartAt H p) x`.
  have h_maps : Set.MapsTo (chartAt ℂ p) (chartAt ℂ p).source
      (extChartAt 𝓘(ℝ, ℂ) p).target := by
    intro x hx
    have hx' : x ∈ (extChartAt 𝓘(ℝ, ℂ) p).source := by
      rw [extChartAt_source]; exact hx
    show (chartAt ℂ p) x ∈ (extChartAt 𝓘(ℝ, ℂ) p).target
    exact (extChartAt 𝓘(ℝ, ℂ) p).map_source hx'
  -- Composition: `partialZBar (bC ∘ chart_p.symm) ∘ chart_p` is ContMDiffOn ∞ on chart_p.source.
  have h_g : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun y : X => partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
                      ((chartAt ℂ p) y))
      (chartAt ℂ p).source := by
    have h_comp := h_pZ_mdiff.comp h_chart h_maps
    exact h_comp
  -- Pointwise: partialZBarManifold (bC) = g on chart_p.source (via reduction).
  have h_eq_on : ∀ x ∈ (chartAt ℂ p).source,
      partialZBarManifold (bC p b) x
        = partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) ((chartAt ℂ p) x) := by
    intro x hx
    show partialZBarManifold (bC p b) x
        = partialZBar (bC p b ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) x)
    exact partialZBarManifold_eq_chart_p_under_const p (bC p b) h_const hx
  -- Bridge via ContMDiffOn congruence.
  exact (h_g.congr h_eq_on) y hy

/-! ## Smoothness of `α` on `X` (under `ChartAtConstantOnSource p`)

The chart-y-based `partialZBarManifold(bC)` and `chartInv` don't have
direct `ContMDiffMul`/`ContMDiffInv₀` instances for `𝓘(ℝ, ℂ)`, so we
build `α`'s smoothness on `chart_p.source` via the chart-p chart
pullback: lift the `ℂ → ℂ` function

  `αHat z := partialZBar (bC ∘ chart_p.symm) z · (z − c₀)⁻¹`

(which is `ContDiffAt ℝ ∞` at chart-p targets `≠ c₀`) through
`chartAt ℂ p` via `ContDiffAt.comp_contMDiffAt`. -/

/-- The chart-p representative `αHat : ℂ → ℂ` for `α`. -/
private noncomputable def αHat (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (z : ℂ) : ℂ :=
  partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z * (z - (chartAt ℂ p) p)⁻¹

/-- Under `ChartAtConstantOnSource p`, on `chart_p.source` we have
`α y = αHat (chart_p y)`. -/
private lemma α_eq_αHat_chart_under_const
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {y : X} (h_y_src : y ∈ (chartAt ℂ p).source) :
    α p b y = αHat p b ((chartAt ℂ p) y) := by
  show partialZBarManifold (bC p b) y * chartInv p y
      = partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) ((chartAt ℂ p) y)
        * ((chartAt ℂ p) y - (chartAt ℂ p) p)⁻¹
  rw [partialZBarManifold_eq_chart_p_under_const p (bC p b) h_const h_y_src,
      chartInv_of_mem_source p y h_y_src]
  -- `(chartAt ℂ p).symm = (extChartAt 𝓘(ℝ, ℂ) p).symm` as functions
  -- (both unfold to the chart's symm with the trivial `𝓘(ℝ, ℂ).symm = id`).
  rfl

/-- `αHat` is `ContDiffAt ℝ ∞` at any `z ∈ chart_p.target` with
`z ≠ c₀`. -/
private lemma αHat_contDiffAt_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    {z : ℂ} (h_z_target : z ∈ (extChartAt 𝓘(ℝ, ℂ) p).target)
    (h_z_ne : z ≠ (chartAt ℂ p) p) :
    ContDiffAt ℝ ∞ (αHat p b) z := by
  -- First factor: chart-side partialZBar smoothness at z.
  have h_pZ_on := partialZBar_bC_chart_p_symm_contDiffOn p b
  have h_target_open : IsOpen (extChartAt 𝓘(ℝ, ℂ) p).target := isOpen_extChartAt_target p
  have h_pZ_at : ContDiffAt ℝ ∞
      (partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)) z :=
    (h_pZ_on z h_z_target).contDiffAt (h_target_open.mem_nhds h_z_target)
  -- Second factor: (· - c₀)⁻¹ smooth at z (≠ c₀).
  have h_nonzero : z - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr h_z_ne
  have h_sub : ContDiffAt ℝ ∞ (fun w : ℂ => w - (chartAt ℂ p) p) z :=
    contDiffAt_id.sub contDiffAt_const
  have h_inv : ContDiffAt ℝ ∞ (fun w : ℂ => (w - (chartAt ℂ p) p)⁻¹) z :=
    h_sub.inv h_nonzero
  -- Product.
  show ContDiffAt ℝ ∞
    (fun w : ℂ => partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) w
                     * (w - (chartAt ℂ p) p)⁻¹) z
  exact h_pZ_at.mul h_inv

/-- `αHat` is `ContDiffAt ℝ ∞` at `c₀ := chart_p p`. (Near `c₀` we have
`bC ∘ chart_p.symm ≡ 1`, so its `partialZBar` is `≡ 0`, hence `αHat
≡ 0` in a nbhd of `c₀` — smooth at `c₀` by `congr_of_eventuallyEq`.) -/
private lemma αHat_contDiffAt_at_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    ContDiffAt ℝ ∞ (αHat p b) ((chartAt ℂ p) p) := by
  -- bC ∘ chart_p.symm ≡ 1 on a nbhd of c₀ (since b ≡ 1 in a nbhd of p,
  -- and chart_p.symm sends c₀ to p).
  have h_target_open : IsOpen (extChartAt 𝓘(ℝ, ℂ) p).target := isOpen_extChartAt_target p
  have h_c₀_in : (chartAt ℂ p) p ∈ (extChartAt 𝓘(ℝ, ℂ) p).target := by
    have hp' : p ∈ (extChartAt 𝓘(ℝ, ℂ) p).source := by
      rw [extChartAt_source]; exact mem_chart_source ℂ p
    exact (extChartAt 𝓘(ℝ, ℂ) p).map_source hp'
  -- Pullback of `b.eventuallyEq_one` through chart.symm.
  have h_bC_eq_one : bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm
      =ᶠ[𝓝 ((chartAt ℂ p) p)] (fun _ : ℂ => (1 : ℂ)) := by
    -- chart.symm tends to p at chart-p p.
    have h_tendsto := extChartAt_symm_tendsto (X := X) p
    -- chart.symm is in `(chartAt ℂ p).symm`-domain etc., simplified by `𝓘(ℝ, ℂ).symm = id`.
    have h_p_eq : (extChartAt 𝓘(ℝ, ℂ) p) p = (chartAt ℂ p) p := rfl
    have h_bC_one : bC p b =ᶠ[𝓝 p] (fun _ : X => (1 : ℂ)) :=
      bC_eventuallyEq_one_near_p p b
    have h_chart_p_eq_extp : (extChartAt 𝓘(ℂ, ℂ) p).symm = (extChartAt 𝓘(ℝ, ℂ) p).symm := rfl
    have h_tendsto_R : Filter.Tendsto (extChartAt 𝓘(ℝ, ℂ) p).symm
        (𝓝 ((chartAt ℂ p) p)) (𝓝 p) := by
      rw [← h_p_eq, ← h_chart_p_eq_extp]; exact h_tendsto
    have h_evEq :
        (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
          =ᶠ[𝓝 ((chartAt ℂ p) p)]
          ((fun _ : X => (1 : ℂ)) ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) :=
      h_bC_one.comp_tendsto h_tendsto_R
    have h_const_comp : ((fun _ : X => (1 : ℂ)) ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
        = (fun _ : ℂ => (1 : ℂ)) := rfl
    rw [h_const_comp] at h_evEq
    exact h_evEq
  -- partialZBar (bC ∘ chart_p.symm) ≡ partialZBar 1 ≡ 0 nearby c₀.
  have h_pZ_zero : partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
      =ᶠ[𝓝 ((chartAt ℂ p) p)] (fun _ : ℂ => (0 : ℂ)) := by
    -- Construct a nbhd of c₀ on which bC ∘ chart_p.symm ≡ 1, on which partialZBar of 1 = 0.
    obtain ⟨U, hU_nhds, hU_eq⟩ := Filter.eventuallyEq_iff_exists_mem.mp h_bC_eq_one
    obtain ⟨V, hV_sub, hV_open, hc₀_in⟩ := mem_nhds_iff.mp hU_nhds
    filter_upwards [hV_open.mem_nhds hc₀_in] with z hz
    show partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z = 0
    -- bC ∘ chart_p.symm ≡ 1 on a nbhd of z (since z ∈ V ⊆ U ⊆ {w | bC..(w) = 1}, open).
    apply partialZBar_eq_zero_of_eventuallyEq_const (c := 1)
    filter_upwards [hV_open.mem_nhds hz] with z' hz'
    exact hU_eq (hV_sub hz')
  -- αHat = pZ · (...)⁻¹. Near c₀: pZ ≡ 0, so αHat ≡ 0 nearby.
  have h_αHat_zero : αHat p b =ᶠ[𝓝 ((chartAt ℂ p) p)] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [h_pZ_zero] with z hz
    show partialZBar (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z * _ = 0
    rw [hz]; ring
  have h_zero_cd : ContDiffAt ℝ ∞ (fun _ : ℂ => (0 : ℂ)) ((chartAt ℂ p) p) :=
    contDiffAt_const
  exact h_zero_cd.congr_of_eventuallyEq h_αHat_zero

/-- Under `ChartAtConstantOnSource p`, `α p b` is `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`
on all of `X`. Pointwise case analysis: on `chart_p.source` use the
chart-p pullback `αHat` (smooth on chart_p.target); off `tsupport b`
the function vanishes in a nbhd. -/
lemma α_contMDiff_under_const
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (α p b) := by
  intro y
  by_cases h_supp : y ∈ tsupport (b : X → ℝ)
  · -- y ∈ tsupport b ⊆ chart_p.source.
    have h_y_src : y ∈ (chartAt ℂ p).source :=
      b.tsupport_subset_chartAt_source h_supp
    -- αHat is ContDiffAt at chart_p y.
    have h_y_in_target : (chartAt ℂ p) y ∈ (extChartAt 𝓘(ℝ, ℂ) p).target := by
      have hx' : y ∈ (extChartAt 𝓘(ℝ, ℂ) p).source := by
        rw [extChartAt_source]; exact h_y_src
      exact (extChartAt 𝓘(ℝ, ℂ) p).map_source hx'
    have h_αHat_at : ContDiffAt ℝ ∞ (αHat p b) ((chartAt ℂ p) y) := by
      by_cases h_yp : y = p
      · rw [h_yp]; exact αHat_contDiffAt_at_pole p b
      · -- y ≠ p in chart_p.source: chart_p y ≠ chart_p p (chart injectivity).
        have h_p_src : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
        have h_inj : (chartAt ℂ p) y ≠ (chartAt ℂ p) p := by
          intro h_eq; exact h_yp ((chartAt ℂ p).injOn h_y_src h_p_src h_eq)
        exact αHat_contDiffAt_off_pole p b h_y_in_target h_inj
    -- chart_p is ContMDiffAt at y.
    have h_chart_on : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (chartAt ℂ p) (chartAt ℂ p).source := contMDiffOn_chart
    have h_src_open : IsOpen (chartAt ℂ p).source := (chartAt ℂ p).open_source
    have h_chart_at : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (chartAt ℂ p) y :=
      (h_chart_on y h_y_src).contMDiffAt (h_src_open.mem_nhds h_y_src)
    -- Composition: αHat ∘ chart_p is ContMDiffAt at y.
    have h_comp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (αHat p b ∘ chartAt ℂ p) y :=
      h_αHat_at.comp_contMDiffAt h_chart_at
    -- α = αHat ∘ chart_p eventually at y (on a nbhd of y in chart_p.source).
    have h_eq : α p b =ᶠ[𝓝 y] (αHat p b ∘ chartAt ℂ p) := by
      filter_upwards [h_src_open.mem_nhds h_y_src] with y' hy'
      exact α_eq_αHat_chart_under_const p b h_const hy'
    exact h_comp.congr_of_eventuallyEq h_eq
  · -- y ∉ tsupport b: α ≡ 0 nearby.
    have h_nbhd : α p b =ᶠ[𝓝 y] (fun _ : X => (0 : ℂ)) :=
      α_eventuallyEq_zero_off_tsupport p b h_supp
    have h_zero : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun _ : X => (0 : ℂ)) y :=
      contMDiff_const.contMDiffAt
    exact h_zero.congr_of_eventuallyEq h_nbhd

/-! ## Chip 2c-Final: Forster §16.9 assembly under chart-const + DBar

The pieces above (`g₀`, `α`, off-pole identity, α smoothness under
`ChartAtConstantOnSource p`) compose with `DBarSolvabilityAtGenusZero X`
and the consolidator `existsSimplePoleGermAtSomePoint_of_chartPullback_data`
(`ExistsSimplePoleGermFromGenusZeroDBarSolvability.lean:413`) to
discharge `ExistsSimplePoleGermAtSomePoint X` on arbitrary X, modulo
the per-`p` structural hypothesis `ChartAtConstantOnSource p` and the
named genus-0 sheaf-cohomology hypothesis. -/

/-! ### Local CR converse from `ContDiffOn ℝ ∞`

`PartialZBarAnalyticConverse.lean`'s `analyticAt_of_contDiffOn_of_partialZBar_eqOn_zero`
takes `ContDiffOn ℝ ⊤ = ContDiffOn ℝ ω`, i.e., real-analytic input. Our
chart pullbacks are `ContDiffOn ℝ ∞` (smooth, not analytic), so we
re-derive the CR converse here from the pointwise public lemma
`differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero`. -/

private lemma analyticAt_of_contDiffOn_infty_of_partialZBar_eqOn_zero
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U)
    (h_dbar : ∀ y ∈ U, partialZBar f y = 0)
    {z : ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  have h_diff_R_on : DifferentiableOn ℝ f U := hf.differentiableOn (by decide)
  have h_diff_C : DifferentiableOn ℂ f U := by
    intro w hw
    have h_diff_R_at : DifferentiableAt ℝ f w :=
      (h_diff_R_on w hw).differentiableAt (hU.mem_nhds hw)
    exact (JacobianChallenge.differentiableAt_complex_of_differentiableAt_real_of_partialZBar_zero
        h_diff_R_at (h_dbar w hw)).differentiableWithinAt
  exact (h_diff_C.analyticOnNhd hU) z hz

/-! ### Chart-y pullback smoothness of `g₀` off the pole

For `y ≠ p`, `g₀ p b ∘ chart_y.symm` is `ℝ`-differentiable at
`chart_y y`. We case-split on whether `y ∈ chart_p.source`. -/

/-- For `y ∉ (chartAt ℂ p).source` (hence `y ∉ tsupport b`), `g₀ p b`
vanishes on the open nbhd `(tsupport b)ᶜ`. -/
private lemma g₀_eventuallyEq_zero_off_chart_p_source
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∉ (chartAt ℂ p).source) :
    g₀ p b =ᶠ[nhds y] (fun _ : X => (0 : ℂ)) := by
  have h_y_not_tsupp : y ∉ tsupport (b : X → ℝ) := fun h =>
    hy (b.tsupport_subset_chartAt_source h)
  have h_bC_zero := bC_eventuallyEq_zero_off_tsupport p b h_y_not_tsupp
  filter_upwards [h_bC_zero] with y' hy'
  show g₀ p b y' = 0
  rw [g₀_eq_bC_mul_chartInv, hy']; ring

/-- Chart-y pullback of `g₀` vanishes on a nbhd of `chart_y y` for
`y ∉ chart_p.source`. -/
private lemma g₀_chart_y_pullback_eventuallyEq_zero_off_chart_p_source
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∉ (chartAt ℂ p).source) :
    (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      =ᶠ[nhds ((extChartAt 𝓘(ℂ, ℂ) y) y)] (fun _ : ℂ => (0 : ℂ)) := by
  have h_tendsto := extChartAt_symm_tendsto y
  have h_evEq := (g₀_eventuallyEq_zero_off_chart_p_source p b hy).comp_tendsto h_tendsto
  have h_const_comp : ((fun _ : X => (0 : ℂ)) ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      = (fun _ : ℂ => (0 : ℂ)) := rfl
  rw [h_const_comp] at h_evEq
  exact h_evEq

/-- `g₀ p b ∘ chart_y.symm` is `ℝ`-differentiable at `chart_y y` for
`y ∉ chart_p.source`. -/
private lemma g₀_chart_y_symm_differentiableAt_off_chart_p_source
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {y : X}
    (hy : y ∉ (chartAt ℂ p).source) :
    DifferentiableAt ℝ (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      ((extChartAt 𝓘(ℂ, ℂ) y) y) := by
  have h_evEq := g₀_chart_y_pullback_eventuallyEq_zero_off_chart_p_source p b hy
  have h_zero_diff : DifferentiableAt ℝ (fun _ : ℂ => (0 : ℂ))
      ((extChartAt 𝓘(ℂ, ℂ) y) y) := differentiableAt_const _
  -- `h_evEq : g₀ ∘ symm =ᶠ const 0`, `h_zero_diff : DifferentiableAt const 0 _`.
  -- `differentiableAt_iff : DifferentiableAt f₀ ↔ DifferentiableAt f₁` given `f₀ =ᶠ f₁`.
  exact (h_evEq.differentiableAt_iff (𝕜 := ℝ)).mpr h_zero_diff

/-- Explicit formula for `g₀ ∘ chart_p.symm` on `chart_p.target`. -/
private lemma g₀_chart_p_pullback_formula
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) p).target) :
    (g₀ p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z
      = (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z * (z - (chartAt ℂ p) p)⁻¹ := by
  have h_in_src : (extChartAt 𝓘(ℝ, ℂ) p).symm z ∈ (extChartAt 𝓘(ℝ, ℂ) p).source :=
    (extChartAt 𝓘(ℝ, ℂ) p).map_target hz
  have h_in_src' : (extChartAt 𝓘(ℝ, ℂ) p).symm z ∈ (chartAt ℂ p).source := by
    rw [← extChartAt_source (I := 𝓘(ℝ, ℂ))]; exact h_in_src
  show g₀ p b ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
      = bC p b ((extChartAt 𝓘(ℝ, ℂ) p).symm z) * (z - (chartAt ℂ p) p)⁻¹
  rw [g₀_eq_bC_mul_chartInv, chartInv_of_mem_source p _ h_in_src']
  have h_right_inv : (chartAt ℂ p) ((extChartAt 𝓘(ℝ, ℂ) p).symm z) = z := by
    show (chartAt ℂ p) ((chartAt ℂ p).symm z) = z
    apply (chartAt ℂ p).right_inv
    have h_tgt_eq : (extChartAt 𝓘(ℝ, ℂ) p).target = (chartAt ℂ p).target := by
      simp [extChartAt]
    rw [← h_tgt_eq]; exact hz
  rw [h_right_inv]

/-- `g₀ ∘ chart_p.symm` is `ContDiffOn ℝ ∞` on `chart_p.target \ {c₀}`. -/
private lemma g₀_chart_p_pullback_contDiffOn_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    ContDiffOn ℝ ∞ (g₀ p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
      ((extChartAt 𝓘(ℝ, ℂ) p).target \ {(chartAt ℂ p) p}) := by
  have h_bC := bC_chart_p_symm_contDiffOn p b
  have h_inv : ContDiffOn ℝ ∞ (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹)
      ((extChartAt 𝓘(ℝ, ℂ) p).target \ {(chartAt ℂ p) p}) := by
    intro z hz
    have h_z_ne : z ≠ (chartAt ℂ p) p := hz.2
    have h_sub : ContDiffAt ℝ ∞ (fun w : ℂ => w - (chartAt ℂ p) p) z :=
      contDiffAt_id.sub contDiffAt_const
    have h_nonzero : z - (chartAt ℂ p) p ≠ 0 := sub_ne_zero.mpr h_z_ne
    exact (h_sub.inv h_nonzero).contDiffWithinAt
  have h_bC_sub : ContDiffOn ℝ ∞ (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
      ((extChartAt 𝓘(ℝ, ℂ) p).target \ {(chartAt ℂ p) p}) :=
    h_bC.mono Set.diff_subset
  have h_prod : ContDiffOn ℝ ∞
      (fun z : ℂ => (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z
                       * (z - (chartAt ℂ p) p)⁻¹)
      ((extChartAt 𝓘(ℝ, ℂ) p).target \ {(chartAt ℂ p) p}) :=
    h_bC_sub.mul h_inv
  apply h_prod.congr
  intro z hz
  exact g₀_chart_p_pullback_formula p b hz.1

/-! ### Forster `f := g₀ - u` and `h := u ∘ chart_p.symm` -/

/-- `f := g₀ p b - u`. -/
private noncomputable def fForster
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (u : X → ℂ) : X → ℂ :=
  g₀ p b - u

/-- `h := u ∘ chart_p.symm`, the analytic correction. -/
private noncomputable def hForster (p : X) (u : X → ℂ) : ℂ → ℂ :=
  u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm

/-! ### ContDiffOn of chart pullbacks of `u` -/

private lemma u_chart_x_symm_contDiffOn
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) (x : X) :
    ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm)
      (extChartAt 𝓘(ℝ, ℂ) x).target := by
  have h_symm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (extChartAt 𝓘(ℝ, ℂ) x).symm
      (extChartAt 𝓘(ℝ, ℂ) x).target := contMDiffOn_extChartAt_symm x
  exact contMDiffOn_iff_contDiffOn.mp (h_u.comp_contMDiffOn h_symm)

private lemma u_chart_x_symm_differentiableAt
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u) (x y : X)
    (hy : y ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℝ (u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) y) := by
  have h_cdo : ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      (extChartAt 𝓘(ℂ, ℂ) x).target := u_chart_x_symm_contDiffOn h_u x
  have h_y_tgt : (extChartAt 𝓘(ℂ, ℂ) x) y ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := by
    have hy' : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source := by
      rw [extChartAt_source]; exact hy
    exact (extChartAt 𝓘(ℂ, ℂ) x).map_source hy'
  have h_tgt_open : IsOpen (extChartAt 𝓘(ℂ, ℂ) x).target := isOpen_extChartAt_target x
  have h_at : ContDiffAt ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) y) :=
    (h_cdo _ h_y_tgt).contDiffAt (h_tgt_open.mem_nhds h_y_tgt)
  exact h_at.differentiableAt (by decide)

/-! ### `∂̄ f = 0` off the pole -/

private lemma g₀_chart_y_symm_differentiableAt_in_chart_p_source
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {y : X} (hy_src : y ∈ (chartAt ℂ p).source) (hyp : y ≠ p) :
    DifferentiableAt ℝ (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      ((extChartAt 𝓘(ℂ, ℂ) y) y) := by
  have h_chart_eq : chartAt ℂ y = chartAt ℂ p := h_const y hy_src
  have h_symm_fn : ((extChartAt 𝓘(ℂ, ℂ) y).symm : ℂ → X)
      = (extChartAt 𝓘(ℂ, ℂ) p).symm := by
    funext z; show (chartAt ℂ y).symm z = (chartAt ℂ p).symm z; rw [h_chart_eq]
  have h_base : (extChartAt 𝓘(ℂ, ℂ) y) y = (extChartAt 𝓘(ℂ, ℂ) p) y := by
    show (chartAt ℂ y) y = (chartAt ℂ p) y; rw [h_chart_eq]
  rw [h_symm_fn, h_base]
  have h_y_tgt : (extChartAt 𝓘(ℂ, ℂ) p) y ∈ (extChartAt 𝓘(ℂ, ℂ) p).target := by
    have hy' : y ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := by
      rw [extChartAt_source]; exact hy_src
    exact (extChartAt 𝓘(ℂ, ℂ) p).map_source hy'
  have h_p_src : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have h_inj : (chartAt ℂ p) y ≠ (chartAt ℂ p) p := fun h =>
    hyp ((chartAt ℂ p).injOn hy_src h_p_src h)
  have h_y_tgt' : (extChartAt 𝓘(ℂ, ℂ) p) y
      ∈ (extChartAt 𝓘(ℝ, ℂ) p).target \ {(chartAt ℂ p) p} := by
    refine ⟨h_y_tgt, ?_⟩
    simp; exact h_inj
  have h_cdo : ContDiffOn ℝ ∞ (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
      ((extChartAt 𝓘(ℂ, ℂ) p).target \ {(chartAt ℂ p) p}) :=
    g₀_chart_p_pullback_contDiffOn_off_pole p b
  have h_set_open : IsOpen ((extChartAt 𝓘(ℂ, ℂ) p).target \ {(chartAt ℂ p) p}) :=
    (isOpen_extChartAt_target p).sdiff isClosed_singleton
  have h_at : ContDiffAt ℝ ∞ (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
      ((extChartAt 𝓘(ℂ, ℂ) p) y) :=
    (h_cdo _ h_y_tgt').contDiffAt (h_set_open.mem_nhds h_y_tgt')
  exact h_at.differentiableAt (by decide)

private lemma g₀_chart_y_symm_differentiableAt_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {y : X} (hyp : y ≠ p) :
    DifferentiableAt ℝ (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm)
      ((extChartAt 𝓘(ℂ, ℂ) y) y) := by
  by_cases hy_src : y ∈ (chartAt ℂ p).source
  · exact g₀_chart_y_symm_differentiableAt_in_chart_p_source p b h_const hy_src hyp
  · exact g₀_chart_y_symm_differentiableAt_off_chart_p_source p b hy_src

private lemma partialZBarManifold_fForster_eq_zero_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (h_u_eq : ∀ x : X, partialZBarManifold u x = α p b x)
    {y : X} (hyp : y ≠ p) :
    partialZBarManifold (fForster p b u) y = 0 := by
  show partialZBarManifold (g₀ p b - u) y = 0
  have h_g₀_diff := g₀_chart_y_symm_differentiableAt_off_pole p b h_const hyp
  have h_u_diff := u_chart_x_symm_differentiableAt h_u y y (mem_chart_source ℂ y)
  rw [partialZBarManifold_sub h_g₀_diff h_u_diff,
      partialZBarManifold_g₀_eq_α_off_pole p b hyp, h_u_eq y]
  ring

/-! ### H1: chart-p pullback equals `(z - c₀)⁻¹ - h(z)` on punctured nbhd -/

private lemma bC_chart_p_symm_eventuallyEq_one_near_c₀
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) :
    (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
      =ᶠ[nhds ((chartAt ℂ p) p)] (fun _ : ℂ => (1 : ℂ)) := by
  -- `extChartAt_symm_tendsto` gives `Tendsto (extChartAt 𝓘(ℂ, ℂ) p).symm
  --   (𝓝 ((extChartAt 𝓘(ℂ, ℂ) p) p)) (𝓝 p)`. `(extChartAt 𝓘(ℂ, ℂ) p) p = chart p p = (extChartAt 𝓘(ℝ, ℂ) p) p`
  -- by defeq, so we can use it directly.
  have h_tendsto : Filter.Tendsto (extChartAt 𝓘(ℝ, ℂ) p).symm
      (𝓝 ((chartAt ℂ p) p)) (𝓝 p) := extChartAt_symm_tendsto p
  have h_bC := bC_eventuallyEq_one_near_p p b
  have h_evEq := h_bC.comp_tendsto h_tendsto
  have h_const_comp : ((fun _ : X => (1 : ℂ)) ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm)
      = (fun _ : ℂ => (1 : ℂ)) := rfl
  rw [h_const_comp] at h_evEq
  exact h_evEq

private lemma fForster_chart_p_eq_simplePole_minus_h
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p) (u : X → ℂ) :
    (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
      =ᶠ[nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ]
      (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹ - hForster p u z) := by
  have h_target_nhds : (extChartAt 𝓘(ℂ, ℂ) p).target ∈ 𝓝 ((chartAt ℂ p) p) :=
    (isOpen_extChartAt_target p).mem_nhds (by
      have hp' : p ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := by
        rw [extChartAt_source]; exact mem_chart_source ℂ p
      exact (extChartAt 𝓘(ℂ, ℂ) p).map_source hp')
  have h_bC_eq := bC_chart_p_symm_eventuallyEq_one_near_c₀ p b
  -- Build the eventually-equality on 𝓝 c₀ implicating z ≠ c₀.
  have h_main : ∀ᶠ z in 𝓝 ((chartAt ℂ p) p),
      z ∈ ({((chartAt ℂ p) p)}ᶜ : Set ℂ) →
        (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z
          = (z - (chartAt ℂ p) p)⁻¹ - hForster p u z := by
    filter_upwards [h_target_nhds, h_bC_eq] with z h_tgt h_bC _h_ne
    -- Use the ℝ form throughout (matches h_bC's natural type).
    show g₀ p b ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
          - u ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
        = (z - (chartAt ℂ p) p)⁻¹ - hForster p u z
    have h_form := g₀_chart_p_pullback_formula p b (z := z) h_tgt
    -- h_form: (g₀ ∘ ext_R.symm) z = (bC ∘ ext_R.symm) z * (z - c₀)⁻¹.
    have h_g₀_val : g₀ p b ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
        = (1 : ℂ) * (z - (chartAt ℂ p) p)⁻¹ := by
      rw [show g₀ p b ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
          = (g₀ p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z from rfl, h_form,
          show (bC p b ∘ (extChartAt 𝓘(ℝ, ℂ) p).symm) z = (1 : ℂ) from h_bC]
    rw [h_g₀_val]
    -- hForster := u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm. And `(ext_ℂ p).symm z = (ext_ℝ p).symm z` defeq.
    show (1 : ℂ) * (z - (chartAt ℂ p) p)⁻¹ - u ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
        = (z - (chartAt ℂ p) p)⁻¹ - hForster p u z
    show (1 : ℂ) * (z - (chartAt ℂ p) p)⁻¹ - u ((extChartAt 𝓘(ℝ, ℂ) p).symm z)
        = (z - (chartAt ℂ p) p)⁻¹ - u ((extChartAt 𝓘(ℂ, ℂ) p).symm z)
    -- Bridge `(ext_ℂ p).symm z = (ext_ℝ p).symm z` (defeq).
    rw [show ((extChartAt 𝓘(ℂ, ℂ) p).symm z : X) = (extChartAt 𝓘(ℝ, ℂ) p).symm z from rfl]
    ring
  -- Convert to nhdsWithin via `eventually_inf_principal`.
  -- `nhdsWithin a s = 𝓝 a ⊓ 𝓟 s` (defeq).
  exact (Filter.eventually_inf_principal.mpr h_main :
    (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
      =ᶠ[nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ]
      (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹ - hForster p u z))

/-! ### h_an: `hForster p u` analytic at `c₀` -/

private lemma partialZBar_u_chart_p_eq_α_chart_pullback
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {u : X → ℂ} (h_u_eq : ∀ x : X, partialZBarManifold u x = α p b x)
    {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target) :
    partialZBar (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z
      = α p b ((extChartAt 𝓘(ℂ, ℂ) p).symm z) := by
  set y : X := (extChartAt 𝓘(ℂ, ℂ) p).symm z with hy_def
  have hy_src : y ∈ (chartAt ℂ p).source := by
    have : y ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := (extChartAt 𝓘(ℂ, ℂ) p).map_target hz
    rwa [extChartAt_source] at this
  have h_red := partialZBarManifold_eq_chart_p_under_const p u h_const hy_src
  have h_chart_p_y : (chartAt ℂ p) y = z := by
    have : (extChartAt 𝓘(ℂ, ℂ) p) y = z := (extChartAt 𝓘(ℂ, ℂ) p).right_inv hz
    exact this
  have h_red' : partialZBarManifold u y
      = partialZBar (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z := by
    show partialZBarManifold u y
        = partialZBar (u ∘ (chartAt ℂ p).symm) z
    rw [h_red, h_chart_p_y]
  rw [← h_red', h_u_eq y]

private lemma hForster_analyticAt_c₀
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (h_u_eq : ∀ x : X, partialZBarManifold u x = α p b x) :
    AnalyticAt ℂ (hForster p u) ((chartAt ℂ p) p) := by
  show AnalyticAt ℂ (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) ((chartAt ℂ p) p)
  obtain ⟨W, hW_sub, hW_open, hpW⟩ : ∃ W : Set X, W ⊆ {y | α p b y = 0} ∧
      IsOpen W ∧ p ∈ W := by
    have h_mem : {y : X | α p b y = 0} ∈ 𝓝 p := by
      filter_upwards [α_eventuallyEq_zero_near_p p b] with y hy; exact hy
    rcases mem_nhds_iff.mp h_mem with ⟨W, hW_sub, hW_open, hpW⟩
    exact ⟨W, hW_sub, hW_open, hpW⟩
  -- Use `chartAt ℂ p` (which IS a `PartialHomeomorph`) for `isOpen_inter_preimage_symm`.
  -- `(extChartAt I p).target = (chartAt ℂ p).target` and similarly for `.symm`,
  -- by defeq for trivial models `𝓘(ℂ, ℂ)`.
  set U : Set ℂ := (chartAt ℂ p).target ∩ (chartAt ℂ p).symm ⁻¹' W
    with hU_def
  have hU_open : IsOpen U :=
    (chartAt ℂ p).isOpen_inter_preimage_symm hW_open
  have hc₀_in_U : (chartAt ℂ p) p ∈ U := by
    refine ⟨?_, ?_⟩
    · exact (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    · show (chartAt ℂ p).symm ((chartAt ℂ p) p) ∈ W
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact hpW
  -- Bridge: `(extChartAt 𝓘(ℂ, ℂ) p).target = (chartAt ℂ p).target` for the trivial
  -- model 𝓘(ℂ, ℂ) (`I.symm = id`, `range I = univ`). Similarly `.symm` is the same fn.
  have h_target_eq : (extChartAt 𝓘(ℂ, ℂ) p).target = (chartAt ℂ p).target := by
    rw [extChartAt_target]; simp
  have h_cdo_target : ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
      (extChartAt 𝓘(ℂ, ℂ) p).target := u_chart_x_symm_contDiffOn h_u p
  -- Restrict to U via mono, then rewrite the chart-form.
  have h_U_sub : U ⊆ (extChartAt 𝓘(ℂ, ℂ) p).target := by
    rw [h_target_eq]; exact inter_subset_left
  have h_cdo_U_ext : ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) U :=
    h_cdo_target.mono h_U_sub
  -- `(extChartAt 𝓘(ℂ, ℂ) p).symm = (chartAt ℂ p).symm` (defeq as functions).
  have h_cdo_U : ContDiffOn ℝ ∞ (u ∘ (chartAt ℂ p).symm) U := h_cdo_U_ext
  have h_dbar_zero : ∀ z ∈ U,
      partialZBar (u ∘ (chartAt ℂ p).symm) z = 0 := by
    intro z hz
    have hz_tgt : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target := h_U_sub hz
    have hz_W : (chartAt ℂ p).symm z ∈ W := hz.2
    show partialZBar (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z = 0
    rw [partialZBar_u_chart_p_eq_α_chart_pullback p b h_const h_u_eq hz_tgt]
    exact hW_sub hz_W
  -- Apply local CR converse (∞-version). Returns AnalyticAt ℂ of (u ∘ chart_p.symm).
  -- Bridge back to extChartAt form.
  have h_an_chart : AnalyticAt ℂ (u ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) :=
    analyticAt_of_contDiffOn_infty_of_partialZBar_eqOn_zero hU_open h_cdo_U
      h_dbar_zero hc₀_in_U
  exact h_an_chart

/-! ### H2: `f ∘ chart_x.symm` analytic at `chart_x x` for `x ≠ p` -/

private lemma fForster_chart_x_analyticAt_caseA
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (h_u_eq : ∀ x : X, partialZBarManifold u x = α p b x)
    {x : X} (hx_src : x ∈ (chartAt ℂ p).source) (hxp : x ≠ p) :
    AnalyticAt ℂ (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) x) := by
  have h_chart_eq : chartAt ℂ x = chartAt ℂ p := h_const x hx_src
  have h_symm_fn : ((extChartAt 𝓘(ℂ, ℂ) x).symm : ℂ → X)
      = (extChartAt 𝓘(ℂ, ℂ) p).symm := by
    funext z; show (chartAt ℂ x).symm z = (chartAt ℂ p).symm z; rw [h_chart_eq]
  have h_base : (extChartAt 𝓘(ℂ, ℂ) x) x = (extChartAt 𝓘(ℂ, ℂ) p) x := by
    show (chartAt ℂ x) x = (chartAt ℂ p) x; rw [h_chart_eq]
  rw [h_symm_fn, h_base]
  set U : Set ℂ := (extChartAt 𝓘(ℂ, ℂ) p).target \ {(chartAt ℂ p) p} with hU_def
  have hU_open : IsOpen U :=
    (isOpen_extChartAt_target p).sdiff isClosed_singleton
  have h_p_src : p ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have h_inj : (chartAt ℂ p) x ≠ (chartAt ℂ p) p := fun h =>
    hxp ((chartAt ℂ p).injOn hx_src h_p_src h)
  have h_x_in_U : (extChartAt 𝓘(ℂ, ℂ) p) x ∈ U := by
    refine ⟨?_, ?_⟩
    · have hx' : x ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := by
        rw [extChartAt_source]; exact hx_src
      exact (extChartAt 𝓘(ℂ, ℂ) p).map_source hx'
    · simp; exact h_inj
  have h_g₀_cdo : ContDiffOn ℝ ∞ (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) U :=
    g₀_chart_p_pullback_contDiffOn_off_pole p b
  have h_u_cdo : ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) U :=
    (u_chart_x_symm_contDiffOn h_u p).mono Set.diff_subset
  have h_f_cdo : ContDiffOn ℝ ∞ (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) U := by
    have h_eq : (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
        = (g₀ p b ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
          - (u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) := by
      funext z; show g₀ p b _ - u _ = g₀ p b _ - u _; rfl
    rw [h_eq]; exact h_g₀_cdo.sub h_u_cdo
  have h_dbar_zero : ∀ z ∈ U,
      partialZBar (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z = 0 := by
    intro z hz
    set y : X := (extChartAt 𝓘(ℂ, ℂ) p).symm z with hy_def
    have hy_src : y ∈ (chartAt ℂ p).source := by
      have : y ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := (extChartAt 𝓘(ℂ, ℂ) p).map_target hz.1
      rwa [extChartAt_source] at this
    have hy_ne_p : y ≠ p := by
      intro heq
      have h_z_eq : (extChartAt 𝓘(ℂ, ℂ) p) y = z :=
        (extChartAt 𝓘(ℂ, ℂ) p).right_inv hz.1
      rw [heq] at h_z_eq
      have h_c₀ : (chartAt ℂ p) p = z := h_z_eq
      have h_z_ne : z ≠ (chartAt ℂ p) p := by simpa using hz.2
      exact h_z_ne h_c₀.symm
    have h_red := partialZBarManifold_eq_chart_p_under_const p (fForster p b u) h_const hy_src
    have h_chart_p_y : (chartAt ℂ p) y = z := by
      have : (extChartAt 𝓘(ℂ, ℂ) p) y = z := (extChartAt 𝓘(ℂ, ℂ) p).right_inv hz.1
      exact this
    have h_man_zero : partialZBarManifold (fForster p b u) y = 0 :=
      partialZBarManifold_fForster_eq_zero_off_pole p b h_const h_u h_u_eq hy_ne_p
    have h_red' : (0 : ℂ) = partialZBar (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z := by
      calc (0 : ℂ) = partialZBarManifold (fForster p b u) y := h_man_zero.symm
        _ = partialZBar (fForster p b u ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) y) := h_red
        _ = partialZBar (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm) z := by
            rw [h_chart_p_y]; rfl
    exact h_red'.symm
  exact analyticAt_of_contDiffOn_infty_of_partialZBar_eqOn_zero hU_open h_f_cdo
    h_dbar_zero h_x_in_U

private lemma fForster_chart_x_analyticAt_caseB
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (h_u_eq : ∀ x : X, partialZBarManifold u x = α p b x)
    {x : X} (hx_src : x ∉ (chartAt ℂ p).source) :
    AnalyticAt ℂ (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) x) := by
  -- V_X must be OPEN: use `chart_x.source ∩ (tsupport b)ᶜ` (both open in X).
  -- For y ∈ V_X, y ∉ tsupport b ⇒ b y = 0 ⇒ bC y = 0 ⇒ g₀ y = 0 (via mul).
  -- Also p ∈ tsupport b (since b p = 1), so y ≠ p on V_X.
  set V_X : Set X := (chartAt ℂ x).source ∩ (tsupport (b : X → ℝ))ᶜ with hV_X_def
  have hV_X_open : IsOpen V_X :=
    (chartAt ℂ x).open_source.inter (isClosed_tsupport _).isOpen_compl
  have hx_in_V_X : x ∈ V_X := by
    refine ⟨mem_chart_source ℂ x, ?_⟩
    intro h_in
    exact hx_src (b.tsupport_subset_chartAt_source h_in)
  -- Image in chart_x.target via chartAt-form (PartialHomeomorph, has isOpen_inter_preimage_symm).
  set U : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' V_X with hU_def
  have hU_open : IsOpen U :=
    (chartAt ℂ x).isOpen_inter_preimage_symm hV_X_open
  have hx_in_U : (chartAt ℂ x) x ∈ U := by
    refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
    show (chartAt ℂ x).symm ((chartAt ℂ x) x) ∈ V_X
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    exact hx_in_V_X
  -- For y ∈ V_X, g₀ y = 0 via bC y = 0.
  have h_g₀_zero_of_y : ∀ y ∈ V_X, g₀ p b y = 0 := by
    intro y hy
    have h_y_not_tsupp : y ∉ tsupport (b : X → ℝ) := hy.2
    have h_bC_zero : bC p b y = 0 := by
      show ((b y : ℝ) : ℂ) = 0
      have h_supp : (b : X → ℝ) y = 0 :=
        Function.notMem_support.mp (fun h => h_y_not_tsupp (subset_closure h))
      rw [h_supp]; norm_cast
    rw [g₀_eq_bC_mul_chartInv, h_bC_zero]; ring
  -- So `f ∘ chart_x.symm` = `-u ∘ chart_x.symm` on U.
  have h_f_eq_neg_u : ∀ z ∈ U,
      (fForster p b u ∘ (chartAt ℂ x).symm) z
        = (-(u ∘ (chartAt ℂ x).symm)) z := by
    intro z hz
    have h_y_in_V : (chartAt ℂ x).symm z ∈ V_X := hz.2
    have h_g₀ : g₀ p b ((chartAt ℂ x).symm z) = 0 := h_g₀_zero_of_y _ h_y_in_V
    show g₀ p b ((chartAt ℂ x).symm z) - u ((chartAt ℂ x).symm z)
        = -(u ((chartAt ℂ x).symm z))
    rw [h_g₀]; ring
  -- ContDiffOn of u ∘ chart_x.symm on U.
  -- Bridge `(extChartAt 𝓘(ℝ, ℂ) x).target = (chartAt ℂ x).target` (trivial model).
  have h_target_eq_x : (extChartAt 𝓘(ℝ, ℂ) x).target = (chartAt ℂ x).target := by
    rw [extChartAt_target]; simp
  have h_U_sub_x : U ⊆ (extChartAt 𝓘(ℝ, ℂ) x).target := by
    rw [h_target_eq_x]; exact inter_subset_left
  have h_u_cdo : ContDiffOn ℝ ∞ (u ∘ (chartAt ℂ x).symm) U :=
    (u_chart_x_symm_contDiffOn h_u x).mono h_U_sub_x
  have h_neg_u_cdo : ContDiffOn ℝ ∞ (-(u ∘ (chartAt ℂ x).symm)) U :=
    h_u_cdo.neg
  -- partialZBar (-u ∘ chart_x.symm) = 0 on U via chart-pullback vanishing helper.
  have h_neg_u_dbar_zero : ∀ z ∈ U,
      partialZBar (-(u ∘ (chartAt ℂ x).symm)) z = 0 := by
    intro z hz
    set y : X := (chartAt ℂ x).symm z with hy_def
    have h_y_in_V : y ∈ V_X := hz.2
    have h_y_in_xsrc : y ∈ (chartAt ℂ x).source := h_y_in_V.1
    have h_y_not_tsupp : y ∉ tsupport (b : X → ℝ) := h_y_in_V.2
    have h_α_y_zero : α p b y = 0 :=
      (α_eventuallyEq_zero_off_tsupport p b h_y_not_tsupp).eq_of_nhds
    have h_man_zero : partialZBarManifold u y = 0 := by
      rw [h_u_eq y, h_α_y_zero]
    have h_u_diff_y := u_chart_x_symm_differentiableAt h_u y y (mem_chart_source ℂ y)
    have h_helper := JacobianChallenge.partialZBarChartPullback_eq_zero_of_partialZBarManifold_zero
      h_y_in_xsrc h_man_zero h_u_diff_y
    have h_chart_x_y : (chartAt ℂ x) y = z := (chartAt ℂ x).right_inv hz.1
    have h_pZ_u : partialZBar (u ∘ (chartAt ℂ x).symm) z = 0 := by
      rw [← h_chart_x_y]; exact h_helper
    rw [partialZBar_neg, h_pZ_u]; ring
  -- AnalyticAt of -u ∘ chart_x.symm at chart_x x via local CR converse (∞).
  have h_neg_u_analytic : AnalyticAt ℂ (-(u ∘ (chartAt ℂ x).symm))
      ((chartAt ℂ x) x) :=
    analyticAt_of_contDiffOn_infty_of_partialZBar_eqOn_zero hU_open h_neg_u_cdo
      h_neg_u_dbar_zero hx_in_U
  -- Bridge `(chartAt ℂ x).symm` ↔ `(extChartAt 𝓘(ℂ, ℂ) x).symm` (defeq).
  -- Transport to f ∘ chart_x.symm via eventually-eq + AnalyticAt.congr.
  have h_evEq : (fForster p b u ∘ (chartAt ℂ x).symm)
      =ᶠ[nhds ((chartAt ℂ x) x)]
      (-(u ∘ (chartAt ℂ x).symm)) := by
    filter_upwards [hU_open.mem_nhds hx_in_U] with z hz
    exact h_f_eq_neg_u z hz
  have h_an_chart : AnalyticAt ℂ (fForster p b u ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) := h_neg_u_analytic.congr h_evEq.symm
  exact h_an_chart

private lemma fForster_chart_x_analyticAt_off_pole
    (p : X) (b : SmoothBumpFunction 𝓘(ℝ, ℂ) p)
    (h_const : ChartAtConstantOnSource p)
    {u : X → ℂ} (h_u : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u)
    (h_u_eq : ∀ x : X, partialZBarManifold u x = α p b x)
    {x : X} (hxp : x ≠ p) :
    AnalyticAt ℂ (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
      ((extChartAt 𝓘(ℂ, ℂ) x) x) := by
  by_cases hx_src : x ∈ (chartAt ℂ p).source
  · exact fForster_chart_x_analyticAt_caseA p b h_const h_u h_u_eq hx_src hxp
  · exact fForster_chart_x_analyticAt_caseB p b h_u h_u_eq hx_src

/-! ### Main theorem: Chip 2c-Final -/

/-- **Chip 2c-Final.** Under the per-`p` structural hypothesis
`ChartAtConstantOnSource p` and the named classical-content hypothesis
`DBarSolvabilityAtGenusZero X` (i.e., `H¹(X, O) = 0` at genus 0), at
`genus X = 0` we obtain `ExistsSimplePoleGermAtSomePoint X` via the
Forster §16.9 cutoff + correction construction. -/
theorem existsSimplePoleGermAtSomePoint_of_dbarSolvability_under_chartConst
    [IsManifold 𝓘(ℝ, ℂ) ⊤ X]
    (p : X) (h_const : ChartAtConstantOnSource p)
    (h_dbar : DBarSolvabilityAtGenusZero X)
    (hg : JacobianChallenge.genus X = 0) :
    ExistsSimplePoleGermAtSomePoint X := by
  let b : SmoothBumpFunction 𝓘(ℝ, ℂ) p := Classical.arbitrary _
  have h_α_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (α p b) :=
    α_contMDiff_under_const p b h_const
  obtain ⟨u, h_u_smooth, h_u_eq⟩ := h_dbar hg (α p b) h_α_smooth
  have h_an : AnalyticAt ℂ (hForster p u) ((chartAt ℂ p) p) :=
    hForster_analyticAt_c₀ p b h_const h_u_smooth h_u_eq
  have h_chart_eq :
      (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) p).symm)
        =ᶠ[nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ]
      (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹ - hForster p u z) :=
    fForster_chart_p_eq_simplePole_minus_h p b u
  have h_off_pole : ∀ x : X, x ≠ p →
      AnalyticAt ℂ (fForster p b u ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
        ((extChartAt 𝓘(ℂ, ℂ) x) x) := fun x hxp =>
    fForster_chart_x_analyticAt_off_pole p b h_const h_u_smooth h_u_eq hxp
  have h_chart_eq' :
      (fForster p b u ∘ (chartAt ℂ p).symm)
        =ᶠ[nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ]
      (fun z : ℂ => (z - (chartAt ℂ p) p)⁻¹ - hForster p u z) := h_chart_eq
  have h_off_pole' : ∀ x : X, x ≠ p →
      AnalyticAt ℂ (fForster p b u ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := h_off_pole
  exact existsSimplePoleGermAtSomePoint_of_chartPullback_data X p
    (fForster p b u) (hForster p u) h_an h_chart_eq' h_off_pole'

end JacobianChallenge.MeromorphicFunctionField

end
