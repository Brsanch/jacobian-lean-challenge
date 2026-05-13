/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartPullbackLocalInverse
import Mathlib.Geometry.Manifold.ContMDiff.Defs

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local manifold inverse for an `ω`-smooth injective map (zz386)

For an `ω`-smooth, globally injective `f : X → Y` between complex
1-manifolds, every point `x : X` admits a local manifold inverse
`f_inv : Y → X` (the chart-conjugate of the analytic local inverse `h`
from zz385) that is `ContMDiffAt … ω` at `f x` and satisfies both
eventual inverse properties around `f x` and `x`.

`f_inv y := (chartAt ℂ x).symm (h ((chartAt ℂ (f x)) y))`.

## Proof outline

The two inverse properties are routine from `h_left`, `h_right` (zz385)
and the chart partial-homeomorphism API. The `ContMDiffAt` claim is
established via `contMDiffAt_iff`: the chart-pulled-back representative
of `f_inv` at `f x` is eventually equal to `h` near `(chartAt ℂ (f x))
(f x)`, and `h` is `AnalyticAt` (hence `ContDiffAt` for `n = ω`).

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature changes to any pre-existing definition or theorem.
-/

noncomputable section

open scoped Topology Manifold ContDiff
open Set Filter Metric

namespace JacobianChallenge
namespace Manifold

universe u v

/-- **Local manifold inverse for an `ω`-smooth injective map.**

For `f : X → Y` `ω`-smooth and globally injective between complex
1-manifolds, and each `x : X`, there is a local inverse `f_inv : Y → X`
near `f x` that is `ω`-smooth at `f x` and inverts `f` on both sides
locally. The witness is `(chartAt ℂ x).symm ∘ h ∘ (chartAt ℂ (f x))`
where `h` is the analytic local inverse from zz385. -/
theorem ContMDiff.exists_local_manifold_inverse_of_injective
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hinj : Function.Injective f) (x : X) :
    ∃ f_inv : Y → X,
      ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f_inv (f x) ∧
      (∀ᶠ y in 𝓝 (f x), f (f_inv y) = y) ∧
      (∀ᶠ z in 𝓝 x, f_inv (f z) = z) := by
  obtain ⟨h, h_an, h_left, h_right⟩ :=
    ContMDiff.chartPullback_localInverse_of_injective hf hinj x
  -- Local names for the charts and key chart points.
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hφ_def
  set ψ : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hψ_def
  set z₀ : ℂ := φ x with hz₀_def
  set w₀ : ℂ := ψ (f x) with hw₀_def
  -- Memberships in source/target.
  have hx_src_φ : x ∈ φ.source := ChartedSpace.mem_chart_source x
  have hfx_src_ψ : f x ∈ ψ.source := ChartedSpace.mem_chart_source (f x)
  have hz₀_tgt_φ : z₀ ∈ φ.target := by
    rw [hz₀_def]; exact φ.map_source hx_src_φ
  have hw₀_tgt_ψ : w₀ ∈ ψ.target := by
    rw [hw₀_def]; exact ψ.map_source hfx_src_ψ
  -- `h w₀ = z₀`.
  have hsymm_z₀ : φ.symm z₀ = x := by
    rw [hz₀_def]; exact φ.left_inv hx_src_φ
  have h_g_at_z₀ :
      ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z₀ = w₀ := by
    show ψ (f (φ.symm z₀)) = w₀
    rw [hsymm_z₀, hw₀_def]
  have h_at_w₀ : h w₀ = z₀ := by
    have h_eval := h_left.self_of_nhds
    rw [h_g_at_z₀] at h_eval
    exact h_eval
  -- The local inverse function.
  refine ⟨fun y => φ.symm (h (ψ y)), ?_, ?_, ?_⟩
  · -- Step A: ContMDiffAt at `f x`.
    rw [contMDiffAt_iff]
    refine ⟨?_, ?_⟩
    · -- Continuity at `f x`.
      have hψ_cont : ContinuousAt (ψ : Y → ℂ) (f x) := ψ.continuousAt hfx_src_ψ
      have hh_cont_at_ψfx : ContinuousAt h (ψ (f x)) := by
        rw [← hw₀_def]; exact h_an.continuousAt
      have hφsymm_cont_at_hψfx : ContinuousAt (φ.symm : ℂ → X) (h (ψ (f x))) := by
        have heq : h (ψ (f x)) = z₀ := by rw [← hw₀_def]; exact h_at_w₀
        rw [heq]; exact φ.continuousAt_symm hz₀_tgt_φ
      have h1 : ContinuousAt (fun y : Y => h (ψ y)) (f x) :=
        ContinuousAt.comp hh_cont_at_ψfx hψ_cont
      exact ContinuousAt.comp hφsymm_cont_at_hψfx h1
    · -- Step B: ContDiffWithinAt of the chart-pullback.
      -- The chart-pullback is
      --   `extChartAt 𝓘(ℂ) ((fun y => φ.symm (h (ψ y))) (f x)) ∘ ... ∘
      --     (extChartAt 𝓘(ℂ) (f x)).symm`
      -- which equals `φ ∘ (fun y => φ.symm (h (ψ y))) ∘ ψ.symm` as functions.
      -- It is eventually equal to `h` near `w₀`, since:
      --   ψ ∘ ψ.symm = id on a nhd of `w₀` in ψ.target,
      --   h continuous at `w₀` with image near `z₀ ∈ φ.target`,
      --   φ ∘ φ.symm = id on a nhd of `z₀` in φ.target.
      -- And `h` is AnalyticAt `w₀` ⇒ ContDiffAt 𝕜 ω `h` `w₀`.
      have hrange : range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ :=
        ModelWithCorners.Boundaryless.range_eq_univ
      rw [hrange, contDiffWithinAt_univ]
      -- Identify base point: `extChartAt 𝓘(ℂ,ℂ) (f x) (f x) = ψ (f x) = w₀`.
      have hbase : extChartAt 𝓘(ℂ, ℂ) (f x) (f x) = w₀ := by
        show (chartAt ℂ (f x)) (f x) = w₀
        rw [← hψ_def, hw₀_def]
      rw [hbase]
      -- Compute `(fun y => φ.symm (h (ψ y))) (f x) = x`.
      have h_self_x : (fun y => φ.symm (h (ψ y))) (f x) = x := by
        show φ.symm (h (ψ (f x))) = x
        rw [← hw₀_def, h_at_w₀, hsymm_z₀]
      -- Rewrite the chart-pullback composition as `w ↦ φ (φ.symm (h (ψ (ψ.symm w))))`.
      have hfun_eq :
          (extChartAt 𝓘(ℂ, ℂ) ((fun y => φ.symm (h (ψ y))) (f x)) ∘
            (fun y => φ.symm (h (ψ y))) ∘ (extChartAt 𝓘(ℂ, ℂ) (f x)).symm)
            = (fun w : ℂ => (φ : X → ℂ) (φ.symm (h (ψ (ψ.symm w))))) := by
        funext w
        show extChartAt 𝓘(ℂ, ℂ) ((fun y => φ.symm (h (ψ y))) (f x))
            ((fun y => φ.symm (h (ψ y))) ((extChartAt 𝓘(ℂ, ℂ) (f x)).symm w))
              = (φ : X → ℂ) (φ.symm (h (ψ (ψ.symm w))))
        rw [h_self_x]
        show (chartAt ℂ x) ((fun y => φ.symm (h (ψ y)))
            ((chartAt ℂ (f x)).symm w))
              = (φ : X → ℂ) (φ.symm (h (ψ (ψ.symm w))))
        rw [← hφ_def, ← hψ_def]
      rw [hfun_eq]
      -- Now show `(fun w => φ (φ.symm (h (ψ (ψ.symm w))))) =ᶠ[𝓝 w₀] h`.
      -- a) `ψ (ψ.symm w) = w` on a nhd of `w₀` (since `w₀ ∈ ψ.target`).
      have hψ_target_nhd : ψ.target ∈ 𝓝 w₀ :=
        ψ.open_target.mem_nhds hw₀_tgt_ψ
      have hψ_id : ∀ᶠ w in 𝓝 w₀, ψ (ψ.symm w) = w := by
        filter_upwards [hψ_target_nhd] with w hw
        exact ψ.right_inv hw
      -- b) `h` is continuous at `w₀` with image landing eventually in `φ.target`.
      have hh_cont : ContinuousAt h w₀ := h_an.continuousAt
      have hφ_target_nhd : φ.target ∈ 𝓝 z₀ :=
        φ.open_target.mem_nhds hz₀_tgt_φ
      have hh_into_target : ∀ᶠ w in 𝓝 w₀, h w ∈ φ.target := by
        have : ∀ᶠ w in 𝓝 w₀, h w ∈ φ.target := by
          have := hh_cont.tendsto
          rw [h_at_w₀] at this
          exact this hφ_target_nhd
        exact this
      -- c) Combine: `φ (φ.symm (h (ψ (ψ.symm w)))) = h w` for w in the intersection.
      have h_eq_h :
          (fun w => φ (φ.symm (h (ψ (ψ.symm w))))) =ᶠ[𝓝 w₀] h := by
        filter_upwards [hψ_id, hh_into_target] with w hψw hhw
        -- Compute step by step.
        rw [hψw]
        -- Now need: φ (φ.symm (h w)) = h w. From h w ∈ φ.target:
        exact φ.right_inv hhw
      -- d) `h` is AnalyticAt w₀ ⇒ ContDiffAt 𝕜 ω.
      have h_h_contDiff : ContDiffAt ℂ ω h w₀ := h_an.contDiffAt
      exact h_h_contDiff.congr_of_eventuallyEq h_eq_h
  · -- Step C: ∀ᶠ y in 𝓝 (f x), f (φ.symm (h (ψ y))) = y.
    -- Strategy: use ψ.injOn on `f (φ.symm (h (ψ y)))` and `y`, both eventually in
    -- ψ.source. The injection-equality input is `ψ (f (φ.symm (h (ψ y)))) = ψ y`,
    -- which follows from `h_right` (the eventual right-inverse on chart pullback).
    have hψ_cont : ContinuousAt (ψ : Y → ℂ) (f x) := ψ.continuousAt hfx_src_ψ
    have hψ_to_w₀ : Tendsto (ψ : Y → ℂ) (𝓝 (f x)) (𝓝 w₀) := by
      rw [hw₀_def]; exact hψ_cont.tendsto
    -- Convert `h_right` (stated at `g z₀`) to be stated at `w₀`.
    rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = w₀
        from h_g_at_z₀] at h_right
    -- Pull `h_right` back along `y ↦ ψ y` to get the eventual identity at `y`.
    have h_right_at_ψy : ∀ᶠ y in 𝓝 (f x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) (h (ψ y)) = ψ y :=
      hψ_to_w₀.eventually h_right
    -- y eventually in ψ.source (since ψ.source is an open nhd of f x).
    have hψsrc_open : ψ.source ∈ 𝓝 (f x) :=
      ψ.open_source.mem_nhds hfx_src_ψ
    -- h(ψ y) eventually in φ.target.
    have h_h_into_target : ∀ᶠ y in 𝓝 (f x), h (ψ y) ∈ φ.target := by
      have hh_into : ∀ᶠ w in 𝓝 w₀, h w ∈ φ.target := by
        have := h_an.continuousAt.tendsto
        rw [h_at_w₀] at this
        exact this (φ.open_target.mem_nhds hz₀_tgt_φ)
      exact hψ_to_w₀.eventually hh_into
    -- The composite `y ↦ f (φ.symm (h (ψ y)))` is continuous at `f x` and equals
    -- `f x` there, hence its values eventually lie in ψ.source.
    have h_fa_src_eventually : ∀ᶠ y in 𝓝 (f x),
        f (φ.symm (h (ψ y))) ∈ ψ.source := by
      have hf_cont : Continuous f := hf.continuous
      have h_hh_at_ψfx : ContinuousAt h (ψ (f x)) := by
        rw [← hw₀_def]; exact h_an.continuousAt
      have h_hψ : ContinuousAt (fun y : Y => h (ψ y)) (f x) :=
        ContinuousAt.comp h_hh_at_ψfx hψ_cont
      have h_φsymm_at : ContinuousAt (φ.symm : ℂ → X) (h (ψ (f x))) := by
        have heq : h (ψ (f x)) = z₀ := by rw [← hw₀_def]; exact h_at_w₀
        rw [heq]; exact φ.continuousAt_symm hz₀_tgt_φ
      have h_inner_cont : ContinuousAt (fun y : Y => φ.symm (h (ψ y))) (f x) :=
        ContinuousAt.comp h_φsymm_at h_hψ
      have h_composite_cont : ContinuousAt (fun y : Y => f (φ.symm (h (ψ y)))) (f x) :=
        ContinuousAt.comp hf_cont.continuousAt h_inner_cont
      -- At y = f x, the composite equals f x.
      have h_val : f (φ.symm (h (ψ (f x)))) = f x := by
        rw [← hw₀_def, h_at_w₀, hsymm_z₀]
      have h_tend : Tendsto (fun y : Y => f (φ.symm (h (ψ y))))
          (𝓝 (f x)) (𝓝 (f x)) := by
        have h_tend_orig := h_composite_cont.tendsto
        rw [h_val] at h_tend_orig
        exact h_tend_orig
      exact h_tend hψsrc_open
    -- Combine the four predicates.
    filter_upwards [h_right_at_ψy, hψsrc_open, h_h_into_target, h_fa_src_eventually]
      with y hψy hy_src _hh_tgt h_fa_src
    -- hψy : ψ (f (φ.symm (h (ψ y)))) = ψ y.
    have hψeq : ψ (f (φ.symm (h (ψ y)))) = ψ y := by
      simpa [Function.comp_apply] using hψy
    -- ψ.injOn on ψ.source.
    exact ψ.injOn h_fa_src hy_src hψeq
  · -- Step D: ∀ᶠ z in 𝓝 x, (φ.symm ∘ h ∘ ψ) (f z) = z.
    -- For z near x, φ z is near z₀, and ψ (f z) = (g) (φ z) eventually equals
    -- `g (φ z)` once φ.symm(φ z) = z (for z ∈ φ.source).
    -- Then `h (ψ (f z)) = h (g (φ z)) = φ z` (from `h_left` applied at φ z).
    -- Then `φ.symm (φ z) = z`.
    have hφ_cont : ContinuousAt (φ : X → ℂ) x := φ.continuousAt hx_src_φ
    have hφ_to_z₀ : Tendsto (φ : X → ℂ) (𝓝 x) (𝓝 z₀) := by
      rw [hz₀_def]; exact hφ_cont.tendsto
    have hφsrc_open : φ.source ∈ 𝓝 x :=
      φ.open_source.mem_nhds hx_src_φ
    -- Pull `h_left` back through `φ`.
    have h_left_at_z : ∀ᶠ z in 𝓝 x,
        h (((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) (φ z)) = φ z := by
      exact hφ_to_z₀.eventually h_left
    filter_upwards [h_left_at_z, hφsrc_open] with z hz hz_src
    -- hz : h ((ψ ∘ f ∘ φ.symm) (φ z)) = φ z
    -- `φ.symm (φ z) = z` since `z ∈ φ.source`.
    have hsymm : φ.symm (φ z) = z := φ.left_inv hz_src
    -- So (ψ ∘ f ∘ φ.symm) (φ z) = ψ (f z).
    have hgφz : ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) (φ z) = ψ (f z) := by
      show ψ (f (φ.symm (φ z))) = ψ (f z)
      rw [hsymm]
    rw [hgφz] at hz
    -- hz : h (ψ (f z)) = φ z. Apply φ.symm:
    have : φ.symm (h (ψ (f z))) = φ.symm (φ z) := by rw [hz]
    rw [hsymm] at this
    exact this

end Manifold
end JacobianChallenge

end
