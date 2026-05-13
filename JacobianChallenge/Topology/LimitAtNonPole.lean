/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemAPI
import JacobianChallenge.Topology.GermLimitLiftSetup
import JacobianChallenge.Divisor.PrincipalDivisor
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics.threshold 100

/-! # Existence of punctured-nhd limit at non-pole points for L(δp)

For `g : X → ℂ` with `IsBoundedByDeltaP p g` and `x ≠ p`, the order
of `g` at `x` is `≥ 0`, so by mathlib's
`tendsto_nhds_of_meromorphicOrderAt_nonneg` the chart-pullback has a
punctured-nhd limit at `chart x`. Pulling this back via
`chartSymm_tendsto_nhdsNE` (already in
`Divisor/PrincipalDivisor.lean`) gives a punctured-nhd limit for `g`
itself at `x`.

This unlocks the `regular_continuousAt` field for the
`LiftToMeromorphicNonzero` discharge: at every non-pole point,
`germLimitLift g` is well-defined as the limit.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Existence of a punctured-nhd limit at non-pole points.** For
`g ∈ L(δp)` and `x ≠ p`, there exists `c : ℂ` with
`g →ᶠ[𝓝[≠] x] c`. -/
theorem exists_tendsto_punctured_of_isBoundedByDeltaP_off_p
    {p : X} {g : X → ℂ}
    (hg : IsBoundedByDeltaP p g) {x : X} (hx : x ≠ p) :
    ∃ c : ℂ, Filter.Tendsto g (𝓝[≠] x) (𝓝 c) := by
  -- Chart-pullback is MeromorphicAt at (chart x) (from g ∈ L(δp)).
  have h_mero_chart : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    hg.mmeromorphicAt x
  -- Order at x is ≥ 0 (from h_off + x ≠ p), so chart-pullback has order ≥ 0.
  have h_ord : 0 ≤ meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    hg.order_nonneg_off x hx
  -- Apply mathlib's tendsto-of-nonneg-order.
  obtain ⟨c, h_tend_chart⟩ :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg h_mero_chart h_ord
  -- Transport back to a punctured-nhd of x via chartSymm_tendsto_nhdsNE.
  refine ⟨c, ?_⟩
  -- We have h_tend_chart : Tendsto (g ∘ chart.symm) (𝓝[≠] (chart x)) (𝓝 c).
  -- And chart_tendsto_nhdsNE x : Tendsto chart (𝓝[≠] x) (𝓝[≠] (chart x)).
  -- Composing: Tendsto (g ∘ chart.symm ∘ chart) (𝓝[≠] x) (𝓝 c).
  -- We need to show g ∘ chart.symm ∘ chart =ᶠ[𝓝[≠] x] g.
  have h_comp : Filter.Tendsto ((g ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x))
      (𝓝[≠] x) (𝓝 c) :=
    h_tend_chart.comp (MeromorphicNonzero.chart_tendsto_nhdsNE x)
  -- (g ∘ chart.symm ∘ chart) = g on chart.source, which is in 𝓝 x.
  have h_src : (chartAt ℂ x).source ∈ 𝓝 x :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  have h_src_NE : (chartAt ℂ x).source ∈ 𝓝[≠] x :=
    nhdsWithin_le_nhds h_src
  have h_eq : ((g ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) =ᶠ[𝓝[≠] x] g := by
    filter_upwards [h_src_NE] with y hy_src
    show g ((chartAt ℂ x).symm ((chartAt ℂ x) y)) = g y
    rw [(chartAt ℂ x).left_inv hy_src]
  exact (Filter.Tendsto.congr' h_eq h_comp)

/-- **`germLimitLift g x = c`** where `c` is the punctured-nhd limit
from the previous theorem. -/
theorem germLimitLift_eq_punctured_limit_of_isBoundedByDeltaP_off_p
    {p : X} {g : X → ℂ}
    (hg : IsBoundedByDeltaP p g) {x : X} (hx : x ≠ p) :
    ∃ c : ℂ, Filter.Tendsto g (𝓝[≠] x) (𝓝 c) ∧
      germLimitLift g x = c := by
  obtain ⟨c, h_tend⟩ :=
    exists_tendsto_punctured_of_isBoundedByDeltaP_off_p hg hx
  refine ⟨c, h_tend, ?_⟩
  -- germLimitLift g x = germLimit g x = c by germLimit_eq_of_tendsto.
  simp [germLimitLift, MeromorphicNonzero.germLimit_eq_of_tendsto h_tend]

end JacobianChallenge

end
