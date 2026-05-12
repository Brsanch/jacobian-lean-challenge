/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereGenus
import JacobianChallenge.Manifold.RiemannSphereSouthChartTendsto

/-! # Full analytic Liouville for `RiemannSphere` 1-form coefficients

This file packages the complete analytic content used in the eventual
proof of `Subsingleton (HolomorphicOneForm RiemannSphere)` (challenge
item 14 reverse direction), independent of the manifold framework.

The chart-coefficient extraction for a `HolomorphicOneForm RiemannSphere`
yields two functions `f, g : ℂ → ℂ` (the north and south coefficients
respectively), with:

* `f` differentiable on all of `ℂ`;
* `g` continuous (in particular, at `0 ∈ ℂ`, which corresponds to
  `∞ ∈ RiemannSphere`);
* the overlap relation `g w = -f w⁻¹ / w^2` on `w ≠ 0` (the cotangent
  bundle transition under `z ↦ 1/z = w`).

From those three inputs Liouville forces `f = 0`: by
`RiemannSphereSouthChartTendsto.tendsto_zero_cocompact_of_southChart_continuous`
the continuity of `g` at `0` gives `Tendsto f (cocompact ℂ) (𝓝 0)`,
which combined with the differentiability of `f` gives `f = 0` via
`RiemannSphereGenus.Liouville_holomorphic_form_chartN_coeff`.

No `sorry`, no `axiom`. Purely analytic content; the chart-coefficient
extraction that produces the three hypotheses lives downstream in the
manifold-glue chase.
-/

set_option diagnostics.threshold 100

open Filter Topology

namespace JacobianChallenge

namespace RiemannSphere

/-- **Full analytic Liouville.** Given two functions `f, g : ℂ → ℂ`
modelling the north / south chart coefficients of a holomorphic 1-form
on the Riemann sphere, with `f` entire, `g` continuous at `0`, and the
overlap relation `g w = -f w⁻¹ / w^2` on `w ≠ 0`, the north-chart
coefficient `f` is identically zero.

This is the analytic core of the Riemann-sphere `Subsingleton`
argument: every step that depends only on `ℂ → ℂ` data and not on the
manifold framework is consolidated here. -/
theorem f_eq_zero_of_southChart_continuous
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_eq : ∀ w : ℂ, w ≠ 0 → g w = -f w⁻¹ / w ^ 2)
    (h_g : ContinuousAt g 0) :
    f = 0 :=
  Liouville_holomorphic_form_chartN_coeff hf
    (tendsto_zero_cocompact_of_southChart_continuous h_eq h_g)

/-- Pointwise corollary of `f_eq_zero_of_southChart_continuous`. -/
theorem f_eq_zero_of_southChart_continuous_apply
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_eq : ∀ w : ℂ, w ≠ 0 → g w = -f w⁻¹ / w ^ 2)
    (h_g : ContinuousAt g 0)
    (z : ℂ) :
    f z = 0 :=
  congrFun (f_eq_zero_of_southChart_continuous hf h_eq h_g) z

/-- Symmetric corollary: under the same hypotheses, the south-chart
coefficient `g` is identically `0` (everywhere, including at `0`).

From `f = 0` and the overlap relation, `g w = 0` on `w ≠ 0`. Continuity
of `g` at `0` then forces `g 0 = 0`, hence `g = 0` everywhere. -/
theorem g_eq_zero_of_southChart_continuous
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (h_eq : ∀ w : ℂ, w ≠ 0 → g w = -f w⁻¹ / w ^ 2)
    (h_g : ContinuousAt g 0) :
    g = 0 := by
  have hf_zero : f = 0 := f_eq_zero_of_southChart_continuous hf h_eq h_g
  -- `g` vanishes off `0` from the overlap relation with `f = 0`.
  have h_off_zero : ∀ w : ℂ, w ≠ 0 → g w = 0 := by
    intro w hw
    have := h_eq w hw
    rw [hf_zero] at this
    simpa using this
  -- Extend to `w = 0` via continuity of `g`.
  have h_at_zero : g 0 = 0 := by
    have h_tendsto_zero :
        Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      exact Filter.Eventually.of_forall (fun w hw => (h_off_zero w hw).symm)
    have h_g' : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) :=
      h_g.tendsto.mono_left nhdsWithin_le_nhds
    have h_nb : (𝓝[≠] (0 : ℂ)).NeBot := inferInstance
    exact tendsto_nhds_unique h_g' h_tendsto_zero
  -- Combine.
  funext w
  by_cases hw : w = 0
  · simp [hw, h_at_zero]
  · simp [h_off_zero w hw]

end RiemannSphere

end JacobianChallenge
