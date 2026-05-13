/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.UniversalGermCoherentFromContinuity
import JacobianChallenge.Topology.LiftDecomposition

set_option diagnostics.threshold 100

/-! # Conditional discharges of `LiftMMeromorphicOn` and `LiftOrderPreserved`
from off-pole continuity

`Topology/LiftDecomposition.lean` (zz362's decomposition) lists five
sub-hypotheses (i)–(v) reducing `LiftToMeromorphicNonzero X` to
elementary statements about `germLimitLift g`. This chip discharges
**inputs (i) `LiftMMeromorphicOn` and (iv) `LiftOrderPreserved`** under
the continuity strengthening
`IsBoundedByDeltaPContinuous` introduced in
`Topology/UniversalGermCoherentFromContinuity.lean`.

## The bridge

Under `IsBoundedByDeltaPContinuous p g`, the previous chip showed
`germLimitLift g =ᶠ[𝓝[≠] x] g` at every `x` (both off-pole and at the
pole — the `at-pole` lemma uses that points in a punctured nhd of `p`
all satisfy `y ≠ p`).

mathlib's `MeromorphicAt.congr` then transports the meromorphy of `g`
to `germLimitLift g`; mathlib's `meromorphicOrderAt_congr` transports
the order. Both are the chart-pullback specialisations the manifold
`MMeromorphicAt` / `mmeromorphicOrderAt` reduce to definitionally.

## What this file delivers

* `germLimitLift_mmeromorphicAt_of_continuous` — preservation of
  `MMeromorphicAt` from `g` to `germLimitLift g` at every point, under
  `IsBoundedByDeltaPContinuous`.
* `germLimitLift_mmeromorphicOrderAt_eq_of_continuous` — preservation
  of `mmeromorphicOrderAt` from `g` to `germLimitLift g` at every
  point.
* `germLimitLift_isBoundedByDeltaP_of_continuous` — under the
  continuity strengthening, `germLimitLift g ∈ IsBoundedByDeltaP p`
  (order pattern preserved). This is exactly input (iv)
  `LiftOrderPreserved` for the strengthened class.
* `liftMMeromorphicOn_of_continuousOff` — input (i) `LiftMMeromorphicOn
  X` discharged under the universal continuity strengthening.
* `liftOrderPreserved_of_continuousOff` — input (iv) `LiftOrderPreserved
  X` discharged under the universal continuity strengthening.

## Architectural status

After this chip, inputs (i) and (iv) of the five-fold decomposition
join input (iii) `LiftRegularContinuousAt` on the
`IsBoundedByDeltaPContinuous` foundation. Three of the five
sub-hypotheses now reduce to a single continuity-off-`p` hypothesis on
the L(δp) class — the operational form of the germ-field refactor.

Inputs (ii) `LiftNonvanishingGerm` and (v) `LiftNotConstant` are
**non-constancy** content: they require identity-theorem reasoning that
goes beyond the EventuallyEq-on-punctured-nhd argument and is the
subject of a separate chip.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## The chart-side EventuallyEq bridge

We carry the manifold-level
`germLimitLift g =ᶠ[𝓝[≠] x] g` through the chart at `x` to obtain the
chart-pullback EventuallyEq that mathlib's `MeromorphicAt.congr` and
`meromorphicOrderAt_congr` require.
-/

/-- **Chart-pullback EventuallyEq from manifold EventuallyEq.** If
`germLimitLift g =ᶠ[𝓝[≠] x] g` on the manifold, the chart pullback
through `(chartAt ℂ x).symm` agrees with `g ∘ (chartAt ℂ x).symm` on a
punctured nhd of `(chartAt ℂ x) x`. -/
lemma chart_pullback_eventuallyEq_of_punctured
    {g h : X → ℂ} {x : X} (hEq : h =ᶠ[𝓝[≠] x] g) :
    h ∘ (chartAt ℂ x).symm =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] g ∘ (chartAt ℂ x).symm := by
  exact (MeromorphicNonzero.chartSymm_tendsto_nhdsNE x).eventually hEq

/-- **EventuallyEq of `germLimitLift g` and `g` at every `x` under the
continuity strengthening.** For `x ≠ p`, this is
`germLimitLift_eventuallyEq_self_off_pole`; for `x = p`, this is
`germLimitLift_eventuallyEq_self_at_pole_of_continuous`. Both pieces
come from `UniversalGermCoherentFromContinuity.lean`. -/
lemma germLimitLift_eventuallyEq_self_everywhere_of_continuous
    {p : X} {g : X → ℂ}
    (h_cts : ∀ y : X, y ≠ p → ContinuousAt g y) (x : X) :
    germLimitLift g =ᶠ[𝓝[≠] x] g := by
  by_cases hxp : x = p
  · -- At the pole: use the at-pole lemma.
    subst hxp
    exact germLimitLift_eventuallyEq_self_at_pole_of_continuous h_cts
  · -- Off the pole: use the off-pole lemma.
    exact germLimitLift_eventuallyEq_self_off_pole h_cts hxp

/-! ## Preservation of `MMeromorphicAt` -/

/-- **Preservation of `MMeromorphicAt` from `g` to `germLimitLift g`**
under the continuity strengthening. Direct application of mathlib's
`MeromorphicAt.congr` to the chart-pullback EventuallyEq. -/
theorem germLimitLift_mmeromorphicAt_of_continuous
    {p : X} {g : X → ℂ}
    (hg : MMeromorphicOn (𝓘(ℂ, ℂ)) g Set.univ)
    (h_cts : ∀ y : X, y ≠ p → ContinuousAt g y) (x : X) :
    MMeromorphicAt (𝓘(ℂ, ℂ)) (germLimitLift g) x := by
  -- Manifold-level EventuallyEq.
  have hEq : germLimitLift g =ᶠ[𝓝[≠] x] g :=
    germLimitLift_eventuallyEq_self_everywhere_of_continuous h_cts x
  -- Chart-pullback.
  have hChartEq : (germLimitLift g) ∘ (chartAt ℂ x).symm
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] g ∘ (chartAt ℂ x).symm :=
    chart_pullback_eventuallyEq_of_punctured hEq
  -- `MMeromorphicAt` unfolds to `MeromorphicAt` of the chart pullback.
  -- Apply `MeromorphicAt.congr` (mathlib `Analysis/Meromorphic/Basic.lean:218`).
  have hg_chart : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    hg x (Set.mem_univ x)
  show MeromorphicAt ((germLimitLift g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  exact hg_chart.congr hChartEq.symm

/-- **`MMeromorphicOn` preservation** as the universal-quantification
form, on all of `X`. -/
theorem germLimitLift_mmeromorphicOn_of_continuous
    {p : X} {g : X → ℂ}
    (hg : MMeromorphicOn (𝓘(ℂ, ℂ)) g Set.univ)
    (h_cts : ∀ y : X, y ≠ p → ContinuousAt g y) :
    MMeromorphicOn (𝓘(ℂ, ℂ)) (germLimitLift g) Set.univ := by
  intro x _
  exact germLimitLift_mmeromorphicAt_of_continuous hg h_cts x

/-! ## Preservation of `mmeromorphicOrderAt` -/

/-- **Preservation of `mmeromorphicOrderAt` from `g` to `germLimitLift
g`** under the continuity strengthening. Application of mathlib's
`meromorphicOrderAt_congr` to the chart-pullback EventuallyEq. -/
theorem germLimitLift_mmeromorphicOrderAt_eq_of_continuous
    {p : X} {g : X → ℂ}
    (h_cts : ∀ y : X, y ≠ p → ContinuousAt g y) (x : X) :
    mmeromorphicOrderAt (𝓘(ℂ, ℂ)) (germLimitLift g) x
      = mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x := by
  have hEq : germLimitLift g =ᶠ[𝓝[≠] x] g :=
    germLimitLift_eventuallyEq_self_everywhere_of_continuous h_cts x
  have hChartEq : (germLimitLift g) ∘ (chartAt ℂ x).symm
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] g ∘ (chartAt ℂ x).symm :=
    chart_pullback_eventuallyEq_of_punctured hEq
  show meromorphicOrderAt ((germLimitLift g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  exact meromorphicOrderAt_congr hChartEq

/-! ## Preservation of `IsBoundedByDeltaP` -/

/-- **`germLimitLift g ∈ IsBoundedByDeltaP p`** under
`IsBoundedByDeltaPContinuous p g`. All three components of the
predicate transport: meromorphy via
`germLimitLift_mmeromorphicOn_of_continuous`, and both order conditions
via `germLimitLift_mmeromorphicOrderAt_eq_of_continuous`. -/
theorem germLimitLift_isBoundedByDeltaP_of_continuous
    {p : X} {g : X → ℂ}
    (hg : IsBoundedByDeltaPContinuous X p g) :
    IsBoundedByDeltaP p (germLimitLift g) := by
  obtain ⟨hg_in, h_cts⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · -- Meromorphy.
    exact germLimitLift_mmeromorphicOn_of_continuous hg_in.mmeromorphicOn h_cts
  · -- Order ≥ 0 off p.
    intro x hx
    rw [germLimitLift_mmeromorphicOrderAt_eq_of_continuous h_cts x]
    exact hg_in.order_nonneg_off x hx
  · -- Order ≥ -1 at p.
    rw [germLimitLift_mmeromorphicOrderAt_eq_of_continuous h_cts p]
    exact hg_in.order_ge_neg_one_at_p

/-! ## Universal discharges (inputs (i) and (iv)) -/

variable (X)

/-- **Input (i) `LiftMMeromorphicOn X` discharged under universal
continuity-off-`p` strengthening of L(δp).** -/
theorem liftMMeromorphicOn_of_continuousOff
    (h_cts_univ : ∀ p : X, ∀ g : X → ℂ,
      IsBoundedByDeltaP p g → ∀ x : X, x ≠ p → ContinuousAt g x) :
    LiftMMeromorphicOn X := by
  intro p g hg
  have h_cts : ∀ y : X, y ≠ p → ContinuousAt g y := h_cts_univ p g hg
  exact germLimitLift_mmeromorphicOn_of_continuous hg.mmeromorphicOn h_cts

/-- **Input (iv) `LiftOrderPreserved X` discharged under universal
continuity-off-`p` strengthening of L(δp).** -/
theorem liftOrderPreserved_of_continuousOff
    (h_cts_univ : ∀ p : X, ∀ g : X → ℂ,
      IsBoundedByDeltaP p g → ∀ x : X, x ≠ p → ContinuousAt g x) :
    LiftOrderPreserved X := by
  intro p g hg
  have h_cts : ∀ y : X, y ≠ p → ContinuousAt g y := h_cts_univ p g hg
  exact germLimitLift_isBoundedByDeltaP_of_continuous ⟨hg, h_cts⟩

end JacobianChallenge

end
