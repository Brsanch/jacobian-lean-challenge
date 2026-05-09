/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.IsManifold.Basic
import JacobianChallenge.Manifold.MeromorphicAt
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.NormPushforwardManifold
import JacobianChallenge.Manifold.NormPushforwardMeromorphyZero

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Translated chart-pullback meromorphy of `normPow g k`
(Phase 1 chip P1.2d-i, ZZ210)

This file ships the **translation form** of ZZ205's
`normPow_mmeromorphicAt_chartPullback_zero`: the chart of `Y` at `y₀` is
not assumed to send `y₀` to `0`. Instead, we subtract `(chartAt ℂ y₀) y₀`
inside `normPow`, so the planar argument vanishes at `y₀`.

## What is shipped

```
theorem normPow_mmeromorphicAt_chartPullback_translated
    {y₀ : Y}
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hg : MeromorphicAt g 0) :
    MMeromorphicAt (𝓘(ℂ, ℂ))
      (fun y : Y => normPow g k ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)) y₀
```

## Proof

Let `w₀ := (chartAt ℂ y₀) y₀`. The function
`y ↦ normPow g k ((chartAt ℂ y₀) y - w₀)` is the chart-pullback
of the planar function `t ↦ normPow g k (t - w₀)`. By
`normPow_mmeromorphicAt_chartPullback_of_planar` (ZZ205), it suffices to
show `MeromorphicAt (fun t => normPow g k (t - w₀)) w₀`. Write this as
`(normPow g k) ∘ (· - w₀)` and apply
`MeromorphicAt.comp_analyticAt`:
* `f := normPow g k`, meromorphic at `0` (ZZ204
  `normPow_meromorphicAt_zero`);
* `g := fun t => t - w₀`, analytic at `w₀` (identity minus a constant),
  with `g w₀ = 0`.
The composition is then meromorphic at `w₀`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No reserved `ω` binder.
* No signature change to any pre-existing definition or theorem.
* Only `JacobianChallenge.lean` import-manifest line is added.
-/

noncomputable section

open scoped Manifold Topology
open Filter Set

namespace JacobianChallenge
namespace Manifold

universe u

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-! ### Planar piece: `normPow g k (· - w₀)` is meromorphic at `w₀`. -/

/-- Translated planar meromorphy of `normPow g k`: composing with the
analytic translation `t ↦ t - w₀` shifts the meromorphy basepoint from
`0` to `w₀`. -/
private lemma normPow_meromorphicAt_translated
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : MeromorphicAt g 0)
    (w₀ : ℂ) :
    MeromorphicAt (fun t : ℂ => normPow g k (t - w₀)) w₀ := by
  -- The translation `T t = t - w₀` is analytic at `w₀` and `T w₀ = 0`.
  have h_translate_analytic : AnalyticAt ℂ (fun t : ℂ => t - w₀) w₀ :=
    analyticAt_id.fun_sub analyticAt_const
  have h_translate_apply : (fun t : ℂ => t - w₀) w₀ = 0 := by
    show w₀ - w₀ = 0
    exact sub_self w₀
  -- Planar headline ZZ204 at `0`.
  have h_planar_zero : MeromorphicAt (normPow g k) 0 :=
    normPow_meromorphicAt_zero hk hg
  -- Rewrite the basepoint to match `comp_analyticAt`.
  have h_planar_at_translated :
      MeromorphicAt (normPow g k) ((fun t : ℂ => t - w₀) w₀) := by
    rw [h_translate_apply]; exact h_planar_zero
  -- Apply `MeromorphicAt.comp_analyticAt`.
  have h_comp :
      MeromorphicAt ((normPow g k) ∘ (fun t : ℂ => t - w₀)) w₀ :=
    h_planar_at_translated.comp_analyticAt h_translate_analytic
  -- The composition is definitionally
  -- `fun t => normPow g k (t - w₀)`.
  exact h_comp

/-! ### Headline: translated chart-pullback meromorphy. -/

/-- **Translated form of `normPow_mmeromorphicAt_chartPullback_zero`.**

For any topological space `Y` charted on `ℂ`, any `y₀ : Y`, and any
`g : ℂ → ℂ` meromorphic at `0` with `1 ≤ k`, the chart-pulled-back
function
`y ↦ normPow g k ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)`
is meromorphic at `y₀` in the chart-pullback (manifold) sense.

The subtraction of `(chartAt ℂ y₀) y₀` translates the planar argument to
`0` at `y₀`, matching the basepoint of `MeromorphicAt g 0`. This removes
ZZ205's `(chartAt ℂ y₀) y₀ = 0` hypothesis, which is not generally true
since charts are not normalised to send their basepoint to `0`. -/
theorem normPow_mmeromorphicAt_chartPullback_translated
    {y₀ : Y}
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hg : MeromorphicAt g 0) :
    MMeromorphicAt (𝓘(ℂ, ℂ))
      (fun y : Y => normPow g k ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)) y₀ := by
  set w₀ : ℂ := (chartAt ℂ y₀) y₀ with hw₀_def
  -- Build the planar piece: `t ↦ normPow g k (t - w₀)` is meromorphic at `w₀`.
  have h_planar : MeromorphicAt (fun t : ℂ => normPow g k (t - w₀)) w₀ :=
    normPow_meromorphicAt_translated hk hg w₀
  -- Rewrite the planar piece's basepoint to the chart image, since
  -- `normPow_mmeromorphicAt_chartPullback_of_planar` expects
  -- `MeromorphicAt _ ((chartAt ℂ y₀) y₀)`.
  have h_planar_at_chart :
      MeromorphicAt (fun t : ℂ => normPow g k (t - w₀)) ((chartAt ℂ y₀) y₀) := by
    rw [← hw₀_def]; exact h_planar
  -- Unfold `MMeromorphicAt` and apply the chart-pullback bridge directly.
  -- We mirror `normPow_mmeromorphicAt_chartPullback_of_planar`'s proof
  -- (ZZ205, line 232 of `NormPushforwardManifold.lean`), but with the
  -- translated planar function `fun t => normPow g k (t - w₀)`.
  show MeromorphicAt
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y - w₀)) ∘ (chartAt ℂ y₀).symm)
      ((chartAt ℂ y₀) y₀)
  -- Eventual equality on `𝓝[≠] ((chartAt ℂ y₀) y₀)` between the chart
  -- pullback and the planar `t ↦ normPow g k (t - w₀)`.
  have h_evEq :
      ((fun y : Y => normPow g k ((chartAt ℂ y₀) y - w₀)) ∘ (chartAt ℂ y₀).symm)
        =ᶠ[𝓝[≠] ((chartAt ℂ y₀) y₀)] (fun t : ℂ => normPow g k (t - w₀)) := by
    -- Use `right_inv` of the chart on its target, restricted to `𝓝[≠]`.
    have h_target_mem :
        (chartAt ℂ y₀).target ∈ nhds ((chartAt ℂ y₀) y₀) :=
      (chartAt ℂ y₀).open_target.mem_nhds
        ((chartAt ℂ y₀).map_source (mem_chart_source ℂ y₀))
    have h_target_mem_NE :
        (chartAt ℂ y₀).target ∈ 𝓝[≠] ((chartAt ℂ y₀) y₀) :=
      mem_nhdsWithin_of_mem_nhds h_target_mem
    refine Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨(chartAt ℂ y₀).target, h_target_mem_NE, ?_⟩
    intro z hz
    show normPow g k ((chartAt ℂ y₀) ((chartAt ℂ y₀).symm z) - w₀)
        = normPow g k (z - w₀)
    rw [(chartAt ℂ y₀).right_inv hz]
  exact h_planar_at_chart.congr h_evEq.symm

end Manifold
end JacobianChallenge

end
