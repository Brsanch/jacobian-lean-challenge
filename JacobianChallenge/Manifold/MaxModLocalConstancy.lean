/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicFoundational
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics.threshold 100

/-! # Chart-level local constancy at a global modulus maximum

For `f : MeromorphicNonzero X` holomorphic everywhere (order `≥ 0`)
and `c : X` a global maximum of `‖f.toFun·‖`, this file shows that
`f.toFun` is eventually equal to `f.toFun c` in a neighbourhood of
`c` (i.e. locally constant near `c`).

The proof is the chart-level Cauchy max-modulus argument:

1. From `MMeromorphicAt I f.toFun c` + `0 ≤ mmeromorphicOrderAt I
   f.toFun c` + `ContinuousAt f.toFun c`, derive
   `AnalyticAt ℂ (f.toFun ∘ chart.symm) (chart c)`
   via `MeromorphicAt.analyticAt`.

2. `AnalyticAt.eventually_analyticAt` upgrades this to analyticity
   in a chart-neighbourhood of `chart c`; combined with
   `AnalyticAt.differentiableAt` we get
   `∀ᶠ z in 𝓝 (chart c), DifferentiableAt ℂ (f.toFun ∘ chart.symm) z`.

3. `c` is a global max of `‖f.toFun·‖` ⇒ `chart c` is a local max of
   `‖(f.toFun ∘ chart.symm) ·‖`.

4. `Complex.eventually_eq_of_isLocalMax_norm` then forces
   `f.toFun ∘ chart.symm =ᶠ[𝓝 (chart c)] const (f.toFun c)`.

5. Transport back through the chart: a neighbourhood of `c` in `X`
   maps into a neighbourhood of `chart c` in `ℂ` via the chart's
   `ContinuousAt`; pulling back the eventual constancy gives
   `f.toFun =ᶠ[𝓝 c] const (f.toFun c)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Filter

namespace JacobianChallenge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- **Chart-pullback `AnalyticAt` from holomorphy.** If `f` has order
`≥ 0` at `x`, then `f.toFun ∘ (chartAt ℂ x).symm` is `AnalyticAt ℂ`
at `(chartAt ℂ x) x`. -/
lemma chartPullback_analyticAt_of_order_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
  -- The chart-pullback is MeromorphicAt at (chart x).
  have h_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x (Set.mem_univ x)
  -- The chart-pullback is ContinuousAt at (chart x).
  -- ContinuousAt f.toFun x  +  chart.symm continuousAt (chart x) ⇒ composition continuous.
  have h_cts_f : ContinuousAt f.toFun x := f.regular_continuousAt x h_nonneg
  have h_symm_cts : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have hx_tgt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    exact (chartAt ℂ x).continuousAt_symm hx_tgt
  -- Composition continuity. Use left_inv: chart.symm (chart x) = x.
  have h_inv : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_cts_comp : ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    rw [show (f.toFun ∘ (chartAt ℂ x).symm) = (f.toFun ∘ (chartAt ℂ x).symm) from rfl]
    refine ContinuousAt.comp ?_ h_symm_cts
    -- ContinuousAt f.toFun (chart.symm (chart x)) = ContinuousAt f.toFun x.
    rw [h_inv]
    exact h_cts_f
  -- Apply MeromorphicAt.analyticAt.
  exact h_mero.analyticAt h_cts_comp

/-- **Eventually `DifferentiableAt`** for the chart pullback under
holomorphy. -/
lemma chartPullback_eventually_differentiableAt_of_order_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (h_nonneg : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      DifferentiableAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z := by
  have h_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    chartPullback_analyticAt_of_order_nonneg f h_nonneg
  -- Upgrade to eventual AnalyticAt + differentiable.
  filter_upwards [h_an.eventually_analyticAt] with z h_an_z
  exact h_an_z.differentiableAt

/-- **`(chartAt c) c` is a local max of the chart-pullback's norm**
from `c` being the global max of `‖f.toFun‖`. -/
lemma chartPullback_isLocalMax_norm_at_max
    (f : MeromorphicNonzero X)
    (_h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    {c : X} (hc_max : IsMaxOn (fun x => ‖f.toFun x‖) Set.univ c) :
    IsLocalMax (fun z => ‖(f.toFun ∘ (chartAt ℂ c).symm) z‖)
      ((chartAt ℂ c) c) := by
  -- For all z, ‖f.toFun (chart.symm z)‖ ≤ ‖f.toFun c‖, and
  -- ‖f.toFun c‖ = ‖(f.toFun ∘ chart.symm) (chart c)‖.
  refine Filter.Eventually.of_forall ?_
  intro z
  -- chart.symm (chart c) = c so the RHS reduces.
  have h_inv : (chartAt ℂ c).symm ((chartAt ℂ c) c) = c :=
    (chartAt ℂ c).left_inv (mem_chart_source ℂ c)
  -- Show ‖f.toFun (chart.symm z)‖ ≤ ‖f.toFun (chart.symm (chart c))‖.
  show ‖f.toFun ((chartAt ℂ c).symm z)‖
      ≤ ‖f.toFun ((chartAt ℂ c).symm ((chartAt ℂ c) c))‖
  rw [h_inv]
  exact hc_max (Set.mem_univ _)

/-- **Chart-level local constancy at the global modulus maximum.**
At a global max `c` of `‖f.toFun‖`, the chart-pullback
`f.toFun ∘ (chartAt ℂ c).symm` is eventually equal to the constant
`f.toFun c` near `(chartAt ℂ c) c`. -/
theorem chartPullback_eventually_eq_const_at_max
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    {c : X} (hc_max : IsMaxOn (fun x => ‖f.toFun x‖) Set.univ c) :
    (f.toFun ∘ (chartAt ℂ c).symm)
      =ᶠ[𝓝 ((chartAt ℂ c) c)] (fun _ => f.toFun c) := by
  -- Eventual differentiability.
  have h_diff : ∀ᶠ z in 𝓝 ((chartAt ℂ c) c),
      DifferentiableAt ℂ (f.toFun ∘ (chartAt ℂ c).symm) z :=
    chartPullback_eventually_differentiableAt_of_order_nonneg f (h_holo c)
  -- Local max of the norm.
  have h_max : IsLocalMax
      (fun z => ‖(f.toFun ∘ (chartAt ℂ c).symm) z‖) ((chartAt ℂ c) c) :=
    chartPullback_isLocalMax_norm_at_max f h_holo hc_max
  -- Apply Complex.eventually_eq_of_isLocalMax_norm.
  -- It returns ∀ᶠ y in 𝓝 (chart c), (f ∘ chart.symm) y = (f ∘ chart.symm) (chart c).
  have h_eq := Complex.eventually_eq_of_isLocalMax_norm h_diff h_max
  -- Convert the right-hand-side from (f ∘ chart.symm) (chart c) to f.toFun c.
  -- chart.symm (chart c) = c, so (f.toFun ∘ chart.symm) (chart c) = f.toFun c.
  have h_inv : (chartAt ℂ c).symm ((chartAt ℂ c) c) = c :=
    (chartAt ℂ c).left_inv (mem_chart_source ℂ c)
  simpa [Function.comp, h_inv] using h_eq

/-- **Global-level local constancy at the maximum.** Transports the
chart-level eventual constancy back to `X`: `f.toFun =ᶠ[𝓝 c]
const (f.toFun c)`. -/
theorem eventually_eq_const_at_max
    (f : MeromorphicNonzero X)
    (h_holo : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x)
    {c : X} (hc_max : IsMaxOn (fun x => ‖f.toFun x‖) Set.univ c) :
    f.toFun =ᶠ[𝓝 c] (fun _ => f.toFun c) := by
  -- Chart-level eventual equality.
  have h_chart : (f.toFun ∘ (chartAt ℂ c).symm)
      =ᶠ[𝓝 ((chartAt ℂ c) c)] (fun _ => f.toFun c) :=
    chartPullback_eventually_eq_const_at_max f h_holo hc_max
  -- Pull back through the chart: the chart at c is continuous at c
  -- (it's a homeomorphism on its source), so `chart` pulls
  -- neighbourhoods of (chart c) back to neighbourhoods of c.
  have h_chart_cts : ContinuousAt (chartAt ℂ c) c :=
    (chartAt ℂ c).continuousAt (mem_chart_source ℂ c)
  -- Apply Filter.Tendsto on `chart c` toward `chart c`: it's
  -- `Tendsto (chart) (𝓝 c) (𝓝 (chart c))`, which is exactly continuity.
  have h_tendsto : Tendsto (chartAt ℂ c) (𝓝 c) (𝓝 ((chartAt ℂ c) c)) :=
    h_chart_cts
  -- Pre-compose the eventual equality with `chart`.
  have h_pre :
      ((f.toFun ∘ (chartAt ℂ c).symm) ∘ (chartAt ℂ c))
        =ᶠ[𝓝 c] ((fun _ => f.toFun c) ∘ (chartAt ℂ c)) := by
    exact h_chart.comp_tendsto h_tendsto
  -- LHS reduces: (f.toFun ∘ chart.symm) ∘ chart = f.toFun on chart.source.
  -- We need eventually-in-𝓝 c, on chart.source (which is in 𝓝 c).
  have h_src : (chartAt ℂ c).source ∈ 𝓝 c :=
    (chartAt ℂ c).open_source.mem_nhds (mem_chart_source ℂ c)
  filter_upwards [h_pre, h_src] with x hxpre hxsrc
  -- LHS of hxpre: (f.toFun ∘ chart.symm) (chart x) = f.toFun ((chart.symm) (chart x)).
  -- Since x ∈ chart.source, chart.symm (chart x) = x, so the LHS is f.toFun x.
  have h_inv_x : (chartAt ℂ c).symm ((chartAt ℂ c) x) = x :=
    (chartAt ℂ c).left_inv hxsrc
  -- hxpre : ((f.toFun ∘ chart.symm) ∘ chart) x = ((fun _ => f.toFun c) ∘ chart) x
  --      = (f.toFun ∘ chart.symm) (chart x) = f.toFun c
  -- Reduce LHS via h_inv_x.
  show f.toFun x = f.toFun c
  have : f.toFun ((chartAt ℂ c).symm ((chartAt ℂ c) x)) = f.toFun c := by
    simpa [Function.comp] using hxpre
  rwa [h_inv_x] at this

end MeromorphicNonzero

end JacobianChallenge

end
