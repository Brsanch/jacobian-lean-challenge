/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartPullbackExtendZero
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Chip 5.3b — smoothness of `chartPullbackZero`

The companion to Sub-chip 5.3a: smoothness of the chart-pullback
extended by zero, as a function `ℂ → ℂ`.

The statement:

```
ContDiff ℝ ∞ (chartPullbackZero x α)
```

under the hypotheses
* `α : X → ℂ` is `ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`,
* `tsupport α ⊆ (chartAt ℂ x).source`,
* `X` is compact,
* `X` is a smooth complex manifold (`IsManifold 𝓘(ℝ, ℂ) ⊤ X`).

The proof glues two pieces:

1. **On `(chartAt ℂ x).target`** (an open set), `chartPullbackZero x α`
   equals the honest composition `α ∘ (chartAt ℂ x).symm`. Manifold-side
   smoothness of `α` plus `contMDiffOn_chart_symm` give the composition
   `ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` on `chart_x.target`, which
   `contMDiffOn_iff_contDiffOn` converts to `ContDiffOn ℝ ∞`.

2. **On `ℂ \ (chartAt ℂ x) '' (tsupport α)`** (the open complement of
   the compact image, see Sub-chip 5.3a), `chartPullbackZero x α`
   is identically zero. Inside `chart_x.target` it's zero because the
   pre-image under `chart_x.symm` lands outside `tsupport α`, hence
   outside `support α`; outside `chart_x.target` it's zero by
   definition.

The open cover `{(chartAt ℂ x).target, ℂ \ chart_x '' (tsupport α)}`
exhausts `ℂ`: any `ζ ∉ chart_x.target` lies in the second set since
the chart image of a closed subset of `chart_x.source` is contained
in `chart_x.target`. So `ContDiffAt ℝ ∞` follows pointwise from the
two local lemmas.

## Main results

* `contDiffOn_chartPullbackZero_target` — `ContDiffOn ℝ ∞` on
  `(chartAt ℂ x).target`.
* `contDiffOn_chartPullbackZero_compl_image` — `ContDiffOn ℝ ∞`
  on the open complement of the chart image of `tsupport α`.
* `contDiff_chartPullbackZero` — **global `ContDiff ℝ ∞`** glued
  from the two local pieces.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℝ, ℂ) ⊤ X]

/-! ## Smoothness on the chart target -/

/-- On the chart target, `chartPullbackZero x α` equals `α ∘ (chartAt ℂ x).symm`,
which is `ContDiffOn ℝ ∞` whenever `α : X → ℂ` is manifold-smooth. -/
theorem contDiffOn_chartPullbackZero_target
    (x : X) (α : X → ℂ)
    (h_α_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α) :
    ContDiffOn ℝ ∞ (chartPullbackZero x α) (chartAt ℂ x).target := by
  -- Step 1: the chart inverse is `ContMDiffOn` at level `⊤ = ω ≥ ∞`.
  -- Bring it down to `∞` via `mono` on the smoothness level.
  have h_symm_smooth_top :
      ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤ (chartAt ℂ x).symm (chartAt ℂ x).target :=
    contMDiffOn_chart_symm
  have h_symm_smooth :
      ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ (chartAt ℂ x).symm (chartAt ℂ x).target :=
    h_symm_smooth_top.of_le (by exact_mod_cast le_top)
  -- Step 2: compose with `α`.
  have h_comp :
      ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞
        (α ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target :=
    h_α_smooth.comp_contMDiffOn h_symm_smooth
  -- Step 3: ℂ → ℂ smoothness; convert ContMDiffOn ↔ ContDiffOn.
  have h_contDiff :
      ContDiffOn ℝ ∞ (α ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target :=
    contMDiffOn_iff_contDiffOn.mp h_comp
  -- Step 4: chartPullbackZero agrees with α ∘ chart.symm on chart.target;
  -- `ContDiffOn.congr` takes the new function via `f₁ x = f x` hypothesis.
  exact h_contDiff.congr (fun ζ hζ =>
    chartPullbackZero_eq_α_chartSymm_on_target x α hζ)

/-! ## Smoothness on the complement of the chart image of `tsupport α` -/

/-- On the open complement of `(chartAt ℂ x) '' (tsupport α)`,
`chartPullbackZero x α` is identically zero, hence trivially `C^∞`. -/
theorem contDiffOn_chartPullbackZero_compl_image
    (x : X) (α : X → ℂ) :
    ContDiffOn ℝ ∞ (chartPullbackZero x α)
      ((chartAt ℂ x) '' (tsupport α))ᶜ := by
  -- The constant-zero function is `ContDiffOn` on any set.
  have h_zero : ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℂ))
      ((chartAt ℂ x) '' (tsupport α))ᶜ := contDiffOn_const
  -- chartPullbackZero ≡ 0 on the complement of the chart image; convert via congr.
  refine h_zero.congr (fun ζ hζ => ?_)
  -- Show `chartPullbackZero x α ζ = (fun _ => 0) ζ = 0`.
  -- `hζ : ζ ∈ ((chartAt ℂ x) '' (tsupport α))ᶜ`
  by_cases hζ_target : ζ ∈ (chartAt ℂ x).target
  · -- ζ ∈ chart.target: chartPullbackZero = α (chart.symm ζ); show α (chart.symm ζ) = 0.
    rw [chartPullbackZero_eq_α_chartSymm_on_target x α hζ_target]
    -- chart.symm ζ ∈ chart.source (from map_target).
    have h_symm_source : (chartAt ℂ x).symm ζ ∈ (chartAt ℂ x).source :=
      (chartAt ℂ x).map_target hζ_target
    -- If chart.symm ζ were in tsupport α, then ζ = chart (chart.symm ζ) ∈ chart '' tsupport α — contradicting hζ.
    have h_not_in_tsupp : (chartAt ℂ x).symm ζ ∉ tsupport α := by
      intro h_in_tsupp
      apply hζ
      refine ⟨(chartAt ℂ x).symm ζ, h_in_tsupp, ?_⟩
      exact (chartAt ℂ x).right_inv hζ_target
    -- α vanishes outside its tsupport (in particular outside its support).
    have h_not_in_supp : (chartAt ℂ x).symm ζ ∉ Function.support α :=
      fun h => h_not_in_tsupp (subset_tsupport α h)
    -- Repackage `not_in_support` as `α (chart.symm ζ) = 0`.
    exact Function.notMem_support.mp h_not_in_supp
  · -- ζ ∉ chart.target: chartPullbackZero ζ = 0 by definition.
    exact chartPullbackZero_eq_zero_off_target x α hζ_target

/-! ## Global smoothness via gluing -/

/-- **Headline.** Under `[CompactSpace X]` and the partition-of-unity
tsupport hypothesis, `chartPullbackZero x α` is `ContDiff ℝ ∞` globally
on `ℂ`. Glues `contDiffOn_chartPullbackZero_target` (on the open chart
target) with `contDiffOn_chartPullbackZero_compl_image` (on the open
complement of the compact chart image of `tsupport α`); these two
open sets cover `ℂ`. -/
theorem contDiff_chartPullbackZero
    [CompactSpace X] (x : X) (α : X → ℂ)
    (h_α_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ α)
    (h_tsupport : tsupport α ⊆ (chartAt ℂ x).source) :
    ContDiff ℝ ∞ (chartPullbackZero x α) := by
  -- Reduce to pointwise ContDiffAt.
  rw [contDiff_iff_contDiffAt]
  intro ζ
  -- The chart image of tsupport α is compact (Sub-chip 5.3a's argument),
  -- hence closed; its complement is open.
  have h_tsupport_closed : IsClosed (tsupport α) := isClosed_tsupport α
  have h_tsupport_compact : IsCompact (tsupport α) := h_tsupport_closed.isCompact
  have h_chart_contOn_tsup : ContinuousOn (chartAt ℂ x) (tsupport α) :=
    (chartAt ℂ x).continuousOn.mono h_tsupport
  have h_image_compact : IsCompact ((chartAt ℂ x) '' (tsupport α)) :=
    h_tsupport_compact.image_of_continuousOn h_chart_contOn_tsup
  have h_image_closed : IsClosed ((chartAt ℂ x) '' (tsupport α)) :=
    h_image_compact.isClosed
  have h_compl_open : IsOpen ((chartAt ℂ x) '' (tsupport α))ᶜ :=
    h_image_closed.isOpen_compl
  -- `chart '' tsupport α ⊆ chart.target` (each element comes from chart.source).
  have h_image_in_target : (chartAt ℂ x) '' (tsupport α) ⊆ (chartAt ℂ x).target := by
    rintro ζ' ⟨y, hy_in_tsupp, hy_eq⟩
    have hy_in_source : y ∈ (chartAt ℂ x).source := h_tsupport hy_in_tsupp
    rw [← hy_eq]
    exact (chartAt ℂ x).map_source hy_in_source
  -- Case-split on whether ζ is in chart.target.
  by_cases hζ_target : ζ ∈ (chartAt ℂ x).target
  · -- Case 1: ζ ∈ chart.target. Use contDiffOn_chartPullbackZero_target.
    have h_target_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
    exact (contDiffOn_chartPullbackZero_target x α h_α_smooth).contDiffAt
      (h_target_open.mem_nhds hζ_target)
  · -- Case 2: ζ ∉ chart.target. Then ζ ∉ chart '' tsupport α (subset).
    have hζ_compl : ζ ∈ ((chartAt ℂ x) '' (tsupport α))ᶜ := by
      intro h_in_image
      exact hζ_target (h_image_in_target h_in_image)
    exact (contDiffOn_chartPullbackZero_compl_image x α).contDiffAt
      (h_compl_open.mem_nhds hζ_compl)

end JacobianChallenge

end
