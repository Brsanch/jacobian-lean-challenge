/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.RamificationIndexPositive
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Analysis.Analytic.Order

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Chain rule for `manifoldRamificationIndex`

For composable `ContMDiff` analytic maps `f : X → Y` and `g : Y → Z` and a
point `x : X`, the manifold ramification indices multiply through
composition:

```
manifoldRamificationIndex (g ∘ f) x =
  manifoldRamificationIndex g (f x) * manifoldRamificationIndex f x
```

The proof uses Mathlib's `AnalyticAt.analyticOrderAt_comp` (the chain rule
for analytic order through composition of analytic functions on `ℂ`),
applied to the chart-pullbacks and reduced through the chart-self
identities `(chartAt ℂ y).symm ∘ chartAt ℂ y = id` near the chart points.

The chain-rule property is the key input that lets the multiplicity-
weighted body of `Jacobian.pullback` satisfy contravariant composition
(`pullback (g ∘ f) = pullback f ∘ pullback g`).

No `sorry`, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge

namespace Manifold

universe u v w

/-- **Chart pullback of a composition equals the composition of chart
pullbacks** (locally, on the appropriate chart targets).

For `f : X → Y` and `g : Y → Z`, the chart-pullback of `g ∘ f`
through the charts at `x` and `g(f x)` agrees, on a neighbourhood of
`(chartAt ℂ x) x`, with the composition of:
- the chart-pullback of `g` through charts at `f x` and `g(f x)`,
- the chart-pullback of `f` through charts at `x` and `f x`.

The local identification uses the chart left-inverse on `(chartAt ℂ (f x))`.
-/
lemma chart_pullback_comp_eventuallyEq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    (f : X → Y) (g : Y → Z) (x : X) (hf_cont : ContinuousAt f x) :
    (fun z : ℂ =>
        ((chartAt ℂ (g (f x))) ∘ (g ∘ f) ∘ (chartAt ℂ x).symm) z)
      =ᶠ[𝓝 ((chartAt ℂ x) x)]
      (fun z : ℂ =>
        (((chartAt ℂ (g (f x))) ∘ g ∘ (chartAt ℂ (f x)).symm) ∘
         ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)) z) := by
  -- Both sides agree on the open set where `(chartAt ℂ x).symm z` lies in
  -- `(chartAt ℂ x).source` (so chart left-inv applies on `f`'s argument)
  -- AND `f ((chartAt ℂ x).symm z)` lies in `(chartAt ℂ (f x)).source` (so
  -- chart left-inv applies on `g`'s argument). The first holds for `z` in
  -- `(chartAt ℂ x).target`; the second by continuity of `f` and the fact
  -- that `f x ∈ source` of `chartAt ℂ (f x)`.
  set eX : OpenPartialHomeomorph X ℂ := chartAt ℂ x with heX
  set eY : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with heY
  set eZ : OpenPartialHomeomorph Z ℂ := chartAt ℂ (g (f x)) with heZ
  -- z₀ = eX x.
  set z₀ : ℂ := eX x with hz₀
  -- The set on which both sides agree.
  have hX_target : (eX.target : Set ℂ) ∈ 𝓝 z₀ :=
    eX.open_target.mem_nhds (eX.map_source (mem_chart_source ℂ x))
  -- f x ∈ eY.source.
  have hfx_eY : f x ∈ eY.source := mem_chart_source ℂ (f x)
  -- The set `f ⁻¹' eY.source` is a nbhd of `x` (continuity of f).
  have hfpre_X : f ⁻¹' eY.source ∈ 𝓝 x :=
    hf_cont (eY.open_source.mem_nhds hfx_eY)
  -- Pull back `f ⁻¹' eY.source` to a nbhd of z₀ in ℂ via eX.symm.
  -- More carefully: we need a nbhd of z₀ on which the composition agrees.
  -- The nbhd is { z ∈ eX.target | eX.symm z ∈ f ⁻¹' eY.source }.
  have hsymm_cont : ContinuousAt (eX.symm : ℂ → X) z₀ :=
    eX.continuousAt_symm (eX.map_source (mem_chart_source ℂ x))
  have hsymm_at_z₀ : eX.symm z₀ = x := eX.left_inv (mem_chart_source ℂ x)
  have hsymm_pre : (eX.symm) ⁻¹' (f ⁻¹' eY.source) ∈ 𝓝 z₀ := by
    apply hsymm_cont
    rw [hsymm_at_z₀]
    exact hfpre_X
  -- Final nbhd: target ∩ (preimage in target).
  have hcombined : eX.target ∩ ((eX.symm) ⁻¹' (f ⁻¹' eY.source)) ∈ 𝓝 z₀ :=
    Filter.inter_mem hX_target hsymm_pre
  -- On this nbhd, both functions agree.
  apply Filter.eventually_of_mem hcombined
  intro z ⟨hz_target, hz_pre⟩
  -- LHS = eZ ((g ∘ f) (eX.symm z)) = eZ (g (f (eX.symm z))).
  -- RHS = eZ (g (eY.symm (eY (f (eX.symm z))))) = eZ (g (f (eX.symm z))) by
  --   eY.left_inv applied to (f (eX.symm z)) ∈ eY.source (which is hz_pre).
  show (eZ ∘ g ∘ f ∘ eX.symm) z = (eZ ∘ g ∘ eY.symm ∘ eY ∘ f ∘ eX.symm) z
  -- Reduce to showing `eY.symm (eY (f (eX.symm z))) = f (eX.symm z)`.
  -- This is eY.left_inv applied to `f (eX.symm z) ∈ eY.source`.
  show eZ (g (f (eX.symm z))) = eZ (g (eY.symm (eY (f (eX.symm z)))))
  congr 2
  exact (eY.left_inv hz_pre).symm

/-- **Chain rule for `manifoldRamificationIndex`** (analytic order
multiplicativity through composition).

For `ContMDiff` non-constant `f : X → Y` and `g : Y → Z` with finite
ramification indices at `x` and `f x`, the ramification index of
`g ∘ f` at `x` is the product of the individual indices. -/
theorem manifoldRamificationIndex_comp_of_finite
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {Z : Type w} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    {f : X → Y} {g : Y → Z} (x : X)
    (hf_an : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    (hg_an : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g (f x))
    (hf_pos : 1 ≤ manifoldRamificationIndex f x)
    (hg_pos : 1 ≤ manifoldRamificationIndex g (f x)) :
    manifoldRamificationIndex (g ∘ f) x =
      manifoldRamificationIndex g (f x) * manifoldRamificationIndex f x := by
  -- Set up the three chart pullbacks: F_f, F_g, F_{g∘f}.
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  set w₀ : ℂ := (chartAt ℂ (f x)) (f x) with hw₀
  set F_f : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_f
  set F_g : ℂ → ℂ := (chartAt ℂ (g (f x))) ∘ g ∘ (chartAt ℂ (f x)).symm with hF_g
  set F_gf : ℂ → ℂ :=
    (chartAt ℂ (g (f x))) ∘ (g ∘ f) ∘ (chartAt ℂ x).symm with hF_gf
  -- F_f z₀ = w₀.
  have hF_f_z₀ : F_f z₀ = w₀ := by
    show (chartAt ℂ (f x)) (f ((chartAt ℂ x).symm ((chartAt ℂ x) x))) = w₀
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  -- F_gf z₀ = F_g (F_f z₀) = F_g w₀.
  have hF_gf_z₀ : F_gf z₀ = F_g w₀ := by
    show (chartAt ℂ (g (f x))) ((g ∘ f) ((chartAt ℂ x).symm ((chartAt ℂ x) x)))
        = F_g w₀
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
    show (chartAt ℂ (g (f x))) (g (f x)) = F_g w₀
    show (chartAt ℂ (g (f x))) (g (f x))
        = (chartAt ℂ (g (f x))) (g ((chartAt ℂ (f x)).symm w₀))
    rw [(chartAt ℂ (f x)).left_inv (mem_chart_source ℂ (f x))]
  -- F_gf =ᶠ F_g ∘ F_f near z₀.
  have h_eventually_eq : F_gf =ᶠ[𝓝 z₀] (F_g ∘ F_f) := by
    have hf_cont : ContinuousAt f x := hf_an.continuousAt
    exact chart_pullback_comp_eventuallyEq f g hf_cont x
  -- Use analyticOrderAt_congr to swap F_gf for F_g ∘ F_f in the order.
  have h_shift_eq :
      (fun z => F_gf z - F_gf z₀) =ᶠ[𝓝 z₀] (fun z => (F_g ∘ F_f) z - F_g w₀) := by
    rw [hF_gf_z₀]
    exact h_eventually_eq.sub (Filter.EventuallyEq.refl _ _)
  -- Order of `F_gf - F_gf z₀` at z₀ = order of `F_g ∘ F_f - F_g w₀` at z₀.
  have hOrd_lift : analyticOrderAt (fun z => F_gf z - F_gf z₀) z₀ =
      analyticOrderAt (fun z => (F_g ∘ F_f) z - F_g w₀) z₀ :=
    analyticOrderAt_congr h_shift_eq
  -- Apply mathlib's `AnalyticAt.analyticOrderAt_comp`. We rewrite
  -- `(F_g ∘ F_f) - F_g w₀` as `(F_g - F_g w₀) ∘ F_f` (using w₀ = F_f z₀).
  have h_recompose :
      (fun z => (F_g ∘ F_f) z - F_g w₀)
        = (fun w => F_g w - F_g w₀) ∘ F_f := by
    funext z; rfl
  rw [h_recompose] at hOrd_lift
  -- F_g and F_f are both analytic.
  have hF_f_an : AnalyticAt ℂ F_f z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiffAt_omega_analyticAt_chart_pullback hf_an
  have hF_g_an : AnalyticAt ℂ F_g w₀ := by
    have := JacobianChallenge.ContMDiff.Owed.degree.contMDiffAt_omega_analyticAt_chart_pullback hg_an
    -- this gives: AnalyticAt ℂ ((chartAt ℂ (g (f x))) ∘ g ∘ (chartAt ℂ (f x)).symm)
    --                          ((chartAt ℂ (f x)) (f x))
    -- which is exactly F_g at w₀.
    convert this using 2
  have hF_g_shift_an : AnalyticAt ℂ (fun w => F_g w - F_g w₀) w₀ :=
    hF_g_an.sub analyticAt_const
  -- Apply chain rule.
  -- mathlib: `analyticOrderAt (h ∘ k) z₀ = analyticOrderAt h (k z₀) * analyticOrderAt (k - k z₀) z₀`
  -- with h := F_g - F_g w₀, k := F_f, z₀ := z₀ here. k z₀ = F_f z₀ = w₀.
  have h_chain :
      analyticOrderAt ((fun w => F_g w - F_g w₀) ∘ F_f) z₀
        = analyticOrderAt (fun w => F_g w - F_g w₀) (F_f z₀)
          * analyticOrderAt (fun z => F_f z - F_f z₀) z₀ := by
    have hF_g_at : AnalyticAt ℂ (fun w => F_g w - F_g w₀) (F_f z₀) := by
      rw [hF_f_z₀]; exact hF_g_shift_an
    exact hF_g_at.analyticOrderAt_comp hF_f_an
  -- Plug in F_f z₀ = w₀.
  rw [hF_f_z₀] at h_chain
  -- Combine.
  rw [hOrd_lift, h_chain]
  -- Goal now: ((order_g · order_f).toNat) = order_g.toNat * order_f.toNat.
  -- This holds when both orders are finite (= when ramification indices are
  -- positive). Use that finite ENat .toNat is a multiplicative.
  unfold manifoldRamificationIndex
  -- Need: 0 < (order_g .toNat) and 0 < (order_f .toNat) ⇒ both orders are finite ⇒
  --   (order_g * order_f).toNat = order_g.toNat * order_f.toNat.
  -- Both 1 ≤ ramification ⇒ orders ≠ ⊤.
  have hord_f_ne_top :
      analyticOrderAt (fun z => F_f z - F_f z₀) z₀ ≠ ⊤ := by
    -- 1 ≤ ramification = order.toNat. If order = ⊤, toNat = 0, contradicting 1 ≤ 0.
    intro h_top
    -- mri f x = (order_f).toNat. h_top says order_f = ⊤. So toNat = 0.
    -- Convert hf_pos to show 1 ≤ 0.
    have : manifoldRamificationIndex f x = 0 := by
      unfold manifoldRamificationIndex
      show (analyticOrderAt _ _).toNat = 0
      rw [show (analyticOrderAt (fun z => F_f z - F_f z₀) z₀) = ⊤ from h_top]
      rfl
    omega
  have hord_g_ne_top :
      analyticOrderAt (fun w => F_g w - F_g w₀) w₀ ≠ ⊤ := by
    intro h_top
    have : manifoldRamificationIndex g (f x) = 0 := by
      unfold manifoldRamificationIndex
      show (analyticOrderAt _ _).toNat = 0
      rw [show (analyticOrderAt (fun w => F_g w - F_g w₀) w₀) = ⊤ from h_top]
      rfl
    omega
  -- Now both finite, so .toNat factors through *.
  obtain ⟨n_g, hn_g⟩ := ENat.ne_top_iff_exists.mp hord_g_ne_top
  obtain ⟨n_f, hn_f⟩ := ENat.ne_top_iff_exists.mp hord_f_ne_top
  rw [← hn_g, ← hn_f]
  rw [← ENat.coe_mul]
  simp [ENat.toNat_coe]
  ring

end Manifold

end JacobianChallenge
