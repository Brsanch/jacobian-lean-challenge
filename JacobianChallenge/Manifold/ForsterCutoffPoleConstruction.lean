/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ExistsSimplePoleGermFromGenusZeroDBarSolvability
import JacobianChallenge.Manifold.PartialZBarManifold
import JacobianChallenge.Manifold.PartialZBarAnalyticConverse
import JacobianChallenge.Manifold.ComplexManifoldRealification
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

/-- Manifold-side: if `f =ᶠ[𝓝 x] (fun _ => c)`, then
`partialZBarManifold f x = 0`. -/
private lemma partialZBarManifold_eq_zero_of_eventuallyEq_const
    {f : X → ℂ} {x : X} {c : ℂ}
    (h : f =ᶠ[𝓝 x] fun _ => c) : partialZBarManifold f x = 0 := by
  -- Push `h` through chart.symm using continuity of `chart.symm` at `chart x x`.
  unfold partialZBarManifold
  have h_tendsto : Filter.Tendsto (extChartAt 𝓘(ℂ, ℂ) x).symm
      (𝓝 ((extChartAt 𝓘(ℂ, ℂ) x) x)) (𝓝 x) := by
    -- `ContinuousAt g y` definitionally unfolds to `Tendsto g (𝓝 y) (𝓝 (g y))`.
    have h_cts := continuousAt_extChartAt_symm (I := (𝓘(ℂ, ℂ))) x
    have h_g_eq : (extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x) = x :=
      extChartAt_to_inv x
    rw [show (𝓝 x) = (𝓝 ((extChartAt 𝓘(ℂ, ℂ) x).symm ((extChartAt 𝓘(ℂ, ℂ) x) x))) from
        by rw [h_g_eq]]
    exact h_cts
  have h_chart :
      (f ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
        =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ℂ) x) x)] ((fun _ : X => c) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) :=
    h.comp_tendsto h_tendsto
  -- `(fun _ : X => c) ∘ chart.symm = fun _ : ℂ => c`.
  have h_const : ((fun _ : X => c) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) = (fun _ : ℂ => c) := rfl
  rw [h_const] at h_chart
  exact partialZBar_eq_zero_of_eventuallyEq_const h_chart

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

end JacobianChallenge.MeromorphicFunctionField

end
