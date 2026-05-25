/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PartitionOfUnitySubordinateToCover
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Support

/-! # Chip 5.3a — chart-pullback extended by zero

For a chart `chartAt ℂ x : X ⊃ U → V ⊆ ℂ` and a function `α : X → ℂ`
whose support is contained in the chart source, the "chart pullback
extended by zero" is the ℂ → ℂ function

```
chartPullbackZero x α ζ :=
  if ζ ∈ (chartAt ℂ x).target then α ((chartAt ℂ x).symm ζ) else 0.
```

This is the natural way to make `α ∘ chart.symm` a globally-defined
ℂ → ℂ function suitable as input to the Cauchy-Pompeiu identity
(Chip 3c-F-4) and the Pompeiu kernel (Chip 1a). The "extended by zero"
device handles two problems with the bare composition
`α ∘ (chartAt ℂ x).symm`:

1. **Undefined behavior of `chart.symm` outside `chart.target`.**
   `PartialHomeomorph.symm` extends `target → source` to a function
   on all of `ℂ`, but outside `target` the value is whatever the
   underlying `PartialEquiv` was constructed with — not guaranteed
   to land outside `chart.source`. Extending by zero on `ℂ \ chart.target`
   forces the function to be 0 there independently of how `chart.symm`
   behaves.

2. **Compact support.** When `tsupport α ⊆ chart.source` and `X` is
   compact, `tsupport α` is a compact subset of the open chart
   source, so its image `(chartAt ℂ x) '' (tsupport α)` is a compact
   subset of `chart.target` — and the support of `chartPullbackZero`
   is contained in this image (`support_subset_image_tsupport`).
   Hence `HasCompactSupport (chartPullbackZero x α)`.

The smoothness of `chartPullbackZero` is the heart of the Sub-chip
5.3b follow-up: it requires bridging manifold-side smoothness of
`α` (`ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`) to chart-side smoothness
(`ContDiff ℝ ∞` of `α ∘ chart.symm` on `chart.target`), and then
gluing across the open cover `{chart.target, ℂ \ chart(tsupport α)}`.
Sub-chip 5.3a ships only the structural / support content (this file).

## Main definitions

* `JacobianChallenge.chartPullbackZero x α` — the chart-pullback
  extended by zero.

## Main results

* `chartPullbackZero_eq_α_chartSymm_on_target` — on `chart.target` the
  extension equals the bare composition `α ∘ chart.symm`.
* `chartPullbackZero_eq_zero_off_target` — off `chart.target` the
  extension is zero.
* `support_chartPullbackZero_subset_chart_image_tsupport` — support
  is contained in `chart '' (tsupport α)`.
* `hasCompactSupport_chartPullbackZero` — under `CompactSpace X` and
  `tsupport α ⊆ chart.source`, the extension has compact support.

No `sorry`, no `axiom`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold Topology
open Set Function

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The chart pullback of `α : X → ℂ` extended by zero on
`ℂ \ (chartAt ℂ x).target`. Inside `(chartAt ℂ x).target` this is the
honest composition `α ∘ (chartAt ℂ x).symm`; outside it is zero
independently of how `(chartAt ℂ x).symm` extends to all of `ℂ`. -/
def chartPullbackZero (x : X) (α : X → ℂ) : ℂ → ℂ :=
  (chartAt ℂ x).target.indicator (α ∘ (chartAt ℂ x).symm)

/-! ## Basic definitional facts -/

/-- Inside `(chartAt ℂ x).target`, the extension equals the bare
chart-pullback composition `α ∘ (chartAt ℂ x).symm`. -/
theorem chartPullbackZero_eq_α_chartSymm_on_target
    (x : X) (α : X → ℂ) {ζ : ℂ} (hζ : ζ ∈ (chartAt ℂ x).target) :
    chartPullbackZero x α ζ = α ((chartAt ℂ x).symm ζ) := by
  unfold chartPullbackZero
  exact Set.indicator_of_mem hζ _

/-- Outside `(chartAt ℂ x).target` the extension is zero. -/
theorem chartPullbackZero_eq_zero_off_target
    (x : X) (α : X → ℂ) {ζ : ℂ} (hζ : ζ ∉ (chartAt ℂ x).target) :
    chartPullbackZero x α ζ = 0 := by
  unfold chartPullbackZero
  exact Set.indicator_of_notMem hζ _

/-- The extension agrees with `α ∘ (chartAt ℂ x).symm` on the open set
`(chartAt ℂ x).target`, in the sense of `Set.EqOn`. -/
theorem chartPullbackZero_eqOn_target (x : X) (α : X → ℂ) :
    Set.EqOn (chartPullbackZero x α) (α ∘ (chartAt ℂ x).symm)
      (chartAt ℂ x).target := by
  intro ζ hζ
  exact chartPullbackZero_eq_α_chartSymm_on_target x α hζ

/-- The extension is identically zero on the complement of
`(chartAt ℂ x).target`. -/
theorem chartPullbackZero_eqOn_zero_compl_target (x : X) (α : X → ℂ) :
    Set.EqOn (chartPullbackZero x α) (fun _ => (0 : ℂ))
      ((chartAt ℂ x).target)ᶜ := by
  intro ζ hζ
  exact chartPullbackZero_eq_zero_off_target x α hζ

/-! ## Algebraic preservation -/

/-- The extension is additive in `α`. -/
theorem chartPullbackZero_add (x : X) (α β : X → ℂ) :
    chartPullbackZero x (α + β)
      = chartPullbackZero x α + chartPullbackZero x β := by
  funext ζ
  by_cases hζ : ζ ∈ (chartAt ℂ x).target
  · simp [chartPullbackZero_eq_α_chartSymm_on_target _ _ hζ, Pi.add_apply]
  · simp [chartPullbackZero_eq_zero_off_target _ _ hζ]

/-- The extension distributes over scalar multiplication by a constant. -/
theorem chartPullbackZero_const_mul (x : X) (c : ℂ) (α : X → ℂ) :
    chartPullbackZero x (fun y => c * α y)
      = fun ζ => c * chartPullbackZero x α ζ := by
  funext ζ
  by_cases hζ : ζ ∈ (chartAt ℂ x).target
  · rw [chartPullbackZero_eq_α_chartSymm_on_target _ _ hζ,
        chartPullbackZero_eq_α_chartSymm_on_target _ _ hζ]
  · rw [chartPullbackZero_eq_zero_off_target _ _ hζ,
        chartPullbackZero_eq_zero_off_target _ _ hζ, mul_zero]

/-! ## Support analysis -/

/-- The (function-theoretic) support of `chartPullbackZero x α` is
contained in `(chartAt ℂ x).target` — anything zero outside `target`
has support inside `target`. -/
theorem support_chartPullbackZero_subset_target
    (x : X) (α : X → ℂ) :
    Function.support (chartPullbackZero x α) ⊆ (chartAt ℂ x).target := by
  intro ζ hζ
  by_contra hζ_not
  apply hζ
  exact chartPullbackZero_eq_zero_off_target x α hζ_not

/-- The support of `chartPullbackZero x α` is contained in the chart
image of the support of `α`: any `ζ` in the support has
`(chartAt ℂ x).symm ζ` in `support α`, and on `chart.target` the
chart is a homeomorphism source ↔ target so `ζ ∈ chart '' (support α)`. -/
theorem support_chartPullbackZero_subset_chart_image_support
    (x : X) (α : X → ℂ) :
    Function.support (chartPullbackZero x α)
      ⊆ (chartAt ℂ x) '' (Function.support α) := by
  intro ζ hζ
  -- ζ ∈ chart.target (from `support_subset_target`).
  have hζ_target : ζ ∈ (chartAt ℂ x).target :=
    support_chartPullbackZero_subset_target x α hζ
  -- chart.symm ζ ∈ chart.source.
  have h_symm_source : (chartAt ℂ x).symm ζ ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).map_target hζ_target
  -- α (chart.symm ζ) ≠ 0 — repackage `hζ`.
  have h_ne_zero : chartPullbackZero x α ζ ≠ 0 := hζ
  have h_α_ne : α ((chartAt ℂ x).symm ζ) ≠ 0 := by
    rw [chartPullbackZero_eq_α_chartSymm_on_target x α hζ_target] at h_ne_zero
    exact h_ne_zero
  refine ⟨(chartAt ℂ x).symm ζ, h_α_ne, ?_⟩
  exact (chartAt ℂ x).right_inv hζ_target

/-- The (closed) topological support of `chartPullbackZero x α` is
contained in the closure of `chart.target` intersected with the
closure of `chart '' (support α)`. Useful form: it lies in the
closed image-or-subset. -/
theorem tsupport_chartPullbackZero_subset_closure_chart_image_support
    (x : X) (α : X → ℂ) :
    tsupport (chartPullbackZero x α) ⊆ closure ((chartAt ℂ x) '' (Function.support α)) := by
  unfold tsupport
  exact closure_mono (support_chartPullbackZero_subset_chart_image_support x α)

/-! ## Compact support under the tsupport hypothesis -/

variable {α : X → ℂ}

/-- **Key compact-support lemma.** When `tsupport α ⊆ (chartAt ℂ x).source`
and `X` is compact, `tsupport α` is a compact subset of the open
chart source. Its image under `chartAt ℂ x` is then a compact subset
of `chart.target`, and `chartPullbackZero x α` is supported inside
this compact image. Hence the extension has compact support in `ℂ`.

The proof:
1. `tsupport α` is closed in `X` (definition).
2. `[CompactSpace X]` + closed ⇒ compact.
3. `chartAt ℂ x` is continuous on `chart.source` ⊇ tsupport α.
4. Continuous image of a compact set is compact.
5. `support (chartPullbackZero x α) ⊆ chart '' (support α) ⊆ chart '' (tsupport α)`
   via `support_subset_tsupport`.
6. So `tsupport (chartPullbackZero x α) ⊆ closure (chart '' (tsupport α))`.
7. `chart '' (tsupport α)` is compact, hence closed in Hausdorff ℂ,
   so closure equals itself.
8. Hence `tsupport (chartPullbackZero x α) ⊆ chart '' (tsupport α)`,
   a compact set. -/
theorem hasCompactSupport_chartPullbackZero
    [CompactSpace X] (x : X)
    (h_tsupport : tsupport α ⊆ (chartAt ℂ x).source) :
    HasCompactSupport (chartPullbackZero x α) := by
  -- Step 1: tsupport α is closed in X.
  have h_tsupport_closed : IsClosed (tsupport α) := isClosed_tsupport α
  -- Step 2: closed in compact ⇒ compact.
  have h_tsupport_compact : IsCompact (tsupport α) :=
    h_tsupport_closed.isCompact
  -- Step 3: chartAt ℂ x is continuous on chart.source.
  have h_chart_contOn : ContinuousOn (chartAt ℂ x) (chartAt ℂ x).source :=
    (chartAt ℂ x).continuousOn
  -- Step 4: chart restricted to tsupport α (a subset of chart.source) is continuous.
  have h_chart_contOn_tsup : ContinuousOn (chartAt ℂ x) (tsupport α) :=
    h_chart_contOn.mono h_tsupport
  -- Step 5: continuous image of compact is compact.
  have h_image_compact : IsCompact ((chartAt ℂ x) '' (tsupport α)) :=
    h_tsupport_compact.image_of_continuousOn h_chart_contOn_tsup
  -- Step 6: support of chartPullbackZero ⊆ chart '' support α
  --        ⊆ chart '' tsupport α (since support ⊆ tsupport).
  have h_support_subset :
      Function.support (chartPullbackZero x α)
        ⊆ (chartAt ℂ x) '' (tsupport α) := by
    refine subset_trans (support_chartPullbackZero_subset_chart_image_support x α) ?_
    exact Set.image_mono (subset_tsupport α)
  -- Step 7: chart '' (tsupport α) is closed (compact in Hausdorff ℂ).
  have h_image_closed : IsClosed ((chartAt ℂ x) '' (tsupport α)) :=
    h_image_compact.isClosed
  -- Step 8: tsupport (chartPullbackZero x α) ⊆ chart '' tsupport α.
  have h_tsup_subset :
      tsupport (chartPullbackZero x α) ⊆ (chartAt ℂ x) '' (tsupport α) := by
    -- `tsupport = closure ∘ support`, and `support ⊆ chart '' tsupport α`
    -- (closed), so `closure support ⊆ closure (chart '' tsupport α) = chart '' tsupport α`.
    calc tsupport (chartPullbackZero x α)
        = closure (Function.support (chartPullbackZero x α)) := rfl
      _ ⊆ closure ((chartAt ℂ x) '' (tsupport α)) :=
          closure_mono h_support_subset
      _ = (chartAt ℂ x) '' (tsupport α) := h_image_closed.closure_eq
  -- Combine: tsupport is a closed subset of a compact set, hence compact.
  exact h_image_compact.of_isClosed_subset (isClosed_tsupport _) h_tsup_subset

end JacobianChallenge

end
