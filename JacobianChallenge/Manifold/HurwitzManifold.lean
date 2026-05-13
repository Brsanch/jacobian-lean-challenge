/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCorollary
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Manifold-level Hurwitz corollary (zz384)

For an `ω`-smooth map `f : X → Y` between complex 1-manifolds (modelled on
`ℂ` via `𝓘(ℂ, ℂ)`) with `f` **globally injective**, the chart-pullback
`(chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm : ℂ → ℂ` has non-vanishing
derivative at `(chartAt ℂ x) x`.

Composition of zz383 (`AnalyticAt.deriv_ne_zero_of_injOn_ball`) with the
existing analyticity bridge `contMDiff_omega_analyticAt_chart_pullback`.

The local-injectivity input for zz383 is supplied by transporting the
global injectivity of `f` through the partial-homeomorphism API of the
two charts: a small ball around `(chartAt ℂ x) x` lies entirely in the
image of `φ.source ∩ f⁻¹ ψ.source` under the chart `φ := chartAt ℂ x`,
and on that ball the composite is injective.

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

/-- **Manifold-level Hurwitz corollary.**

For `f : X → Y` an `ω`-smooth map between complex 1-manifolds with `f`
globally injective, the chart-pullback at any point `x : X` has non-zero
derivative at the chart image `(chartAt ℂ x) x`. -/
theorem ContMDiff.deriv_chart_pullback_ne_zero_of_injective
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hinj : Function.Injective f) (x : X) :
    deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 := by
  -- Notation: φ for the chart at x, ψ for the chart at f x, g for the composite.
  set φ : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hφ_def
  set ψ : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hψ_def
  set g : ℂ → ℂ := ψ ∘ f ∘ φ.symm with hg_def
  -- Step 1: analyticity of `g` at the chart image `φ x` via the existing bridge.
  have h_an : AnalyticAt ℂ g (φ x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- Step 2: identify an open neighbourhood `U ⊆ X` of `x` mapped by `φ` to an
  -- open set in `ℂ` and by `f` into `ψ.source`.
  have hx_mem_φ : x ∈ φ.source := ChartedSpace.mem_chart_source x
  have hfx_mem_ψ : f x ∈ ψ.source := ChartedSpace.mem_chart_source (f x)
  have hf_cont : Continuous f := hf.continuous
  -- `f⁻¹ ψ.source` is open in X.
  have h_fpre_open : IsOpen (f ⁻¹' ψ.source) :=
    ψ.open_source.preimage hf_cont
  -- Define `U := φ.source ∩ f⁻¹ ψ.source`; it is open and contains x.
  set U : Set X := φ.source ∩ f ⁻¹' ψ.source with hU_def
  have hU_open : IsOpen U := φ.open_source.inter h_fpre_open
  have hx_mem_U : x ∈ U := ⟨hx_mem_φ, hfx_mem_ψ⟩
  -- φ maps U to an open subset of ℂ containing φ x.
  have hU_sub_source : U ⊆ φ.source := inter_subset_left
  have hφ_U_open : IsOpen (φ '' U) :=
    φ.isOpen_image_of_subset_source hU_open hU_sub_source
  have hφx_mem : φ x ∈ φ '' U := ⟨x, hx_mem_U, rfl⟩
  -- Choose a ball around `φ x` contained in `φ '' U`.
  rw [Metric.isOpen_iff] at hφ_U_open
  obtain ⟨R, hR_pos, hR_sub⟩ := hφ_U_open (φ x) hφx_mem
  -- Step 3: prove `g` is injective on `Metric.ball (φ x) R`.
  have h_injOn : Set.InjOn g (Metric.ball (φ x) R) := by
    intro z₁ hz₁ z₂ hz₂ hgz
    -- z₁, z₂ ∈ φ '' U so each is φ of some U-element.
    obtain ⟨y₁, hy₁_U, hy₁_eq⟩ := hR_sub hz₁
    obtain ⟨y₂, hy₂_U, hy₂_eq⟩ := hR_sub hz₂
    -- y₁, y₂ ∈ φ.source.
    have hy₁_φ : y₁ ∈ φ.source := hy₁_U.1
    have hy₂_φ : y₂ ∈ φ.source := hy₂_U.1
    -- φ.symm z₁ = y₁ and φ.symm z₂ = y₂.
    have hsymm_z₁ : φ.symm z₁ = y₁ := by rw [← hy₁_eq]; exact φ.left_inv hy₁_φ
    have hsymm_z₂ : φ.symm z₂ = y₂ := by rw [← hy₂_eq]; exact φ.left_inv hy₂_φ
    -- f y₁ ∈ ψ.source and f y₂ ∈ ψ.source.
    have hfy₁ : f y₁ ∈ ψ.source := hy₁_U.2
    have hfy₂ : f y₂ ∈ ψ.source := hy₂_U.2
    -- Unfold `g z₁ = g z₂`.
    have hgz' : ψ (f y₁) = ψ (f y₂) := by
      have := hgz
      simp only [hg_def, Function.comp_apply, hsymm_z₁, hsymm_z₂] at this
      exact this
    -- ψ injective on ψ.source.
    have hfeq : f y₁ = f y₂ := ψ.injOn hfy₁ hfy₂ hgz'
    -- f globally injective ⇒ y₁ = y₂.
    have hyeq : y₁ = y₂ := hinj hfeq
    -- Hence z₁ = z₂.
    rw [← hy₁_eq, ← hy₂_eq, hyeq]
  -- Step 4: apply zz383 to conclude.
  exact AnalyticAt.deriv_ne_zero_of_injOn_ball h_an hR_pos h_injOn

/-- `IsManifold ω`-flavoured restatement: identical to
`ContMDiff.deriv_chart_pullback_ne_zero_of_injective` but stated with the
optional `IsManifold` hypothesis for downstream convenience. The
`IsManifold` instance is not needed for the proof — analyticity comes
solely from `ContMDiff … ω`. -/
theorem ContMDiff.deriv_chart_pullback_ne_zero_of_injective_isManifold
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hinj : Function.Injective f) (x : X) :
    deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
  ContMDiff.deriv_chart_pullback_ne_zero_of_injective hf hinj x

end Manifold
end JacobianChallenge

end
