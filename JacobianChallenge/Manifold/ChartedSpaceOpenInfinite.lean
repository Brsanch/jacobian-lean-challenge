/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic

set_option diagnostics.threshold 100

/-! # Any open neighbourhood in a complex-1-manifold is infinite

A clean foundation lemma for the chart-finiteness argument inside
`NearbyRegularValueExists`. For `[ChartedSpace ℂ Y]`, every open set
`V ⊆ Y` containing some point `y₀` is infinite.

Proof: pull `V` back through the chart at `y₀` to an open set in `ℂ`
containing `(chartAt ℂ y₀) y₀`. Open sets of `ℂ` containing a point
are infinite (`Module.punctured_nhds_neBot`). Since the chart is a
partial homeomorphism from an open subset of `Y` to an open subset of
`ℂ`, the chart restricted to its source is injective, so the preimage
of an infinite set under an injection is infinite, and therefore `V`
itself is infinite.

No `sorry`, no `axiom`. Pure topology + mathlib-standard manipulations.
-/

open Set Filter Topology Metric
open scoped Manifold

noncomputable section

namespace JacobianChallenge

universe v

variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **Punctured-neighbourhood non-triviality at any `z : ℂ`.** -/
private lemma neBot_nhdsNE_complex_local (z : ℂ) : Filter.NeBot (𝓝[≠] z) :=
  Module.punctured_nhds_neBot ℂ ℂ z

/-- **Open sets in `ℂ` containing a point are infinite.** -/
private lemma isOpen_complex_set_infinite_of_mem_local
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : U.Infinite := by
  haveI : Filter.NeBot (𝓝[≠] z) := neBot_nhdsNE_complex_local z
  exact infinite_of_mem_nhds z (hU.mem_nhds hz)

/-- **Any open neighbourhood of a point in a charted complex 1-manifold
is infinite.** -/
theorem open_nbhd_infinite_of_chartedSpace_complex
    {V : Set Y} (hV_open : IsOpen V) {y₀ : Y} (hy₀ : y₀ ∈ V) :
    V.Infinite := by
  -- Chart at y₀: c : Y → ℂ, with source ∋ y₀ and target an open set of ℂ.
  set c : OpenPartialHomeomorph Y ℂ := chartAt ℂ y₀ with hc_def
  have hy₀_src : y₀ ∈ c.source := mem_chart_source ℂ y₀
  have hcy₀_tgt : c y₀ ∈ c.target := c.map_source hy₀_src
  -- W := c '' (V ∩ c.source) is open in ℂ and contains c y₀.
  have hVc_open : IsOpen (V ∩ c.source) := hV_open.inter c.open_source
  have hVc_open_image : IsOpen (c '' (V ∩ c.source)) := by
    refine c.isOpen_image_of_subset_source hVc_open ?_
    exact inter_subset_right
  have hcy₀_in : c y₀ ∈ c '' (V ∩ c.source) :=
    ⟨y₀, ⟨hy₀, hy₀_src⟩, rfl⟩
  -- Image is infinite.
  have hImg_inf : (c '' (V ∩ c.source)).Infinite :=
    isOpen_complex_set_infinite_of_mem_local hVc_open_image hcy₀_in
  -- c is injective on c.source, hence on V ∩ c.source.
  have hInj : Set.InjOn c (V ∩ c.source) :=
    c.injOn.mono inter_subset_right
  -- An injection from V ∩ c.source onto an infinite set forces V ∩ c.source infinite.
  have hVc_inf : (V ∩ c.source).Infinite := by
    by_contra hFin
    rw [Set.not_infinite] at hFin
    exact hImg_inf (hFin.image c)
  -- V ⊇ V ∩ c.source, so V is infinite.
  exact hVc_inf.mono inter_subset_left

end JacobianChallenge

end
