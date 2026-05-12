/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! # South-chart-to-cocompact tendsto for `RiemannSphere` 1-form coefficients

This is a purely complex-analytic sub-chip toward
`Subsingleton (HolomorphicOneForm RiemannSphere)` (the gating input for
challenge item 14, reverse direction, in
`Manifold/RiemannSphereGenus.lean`).

The chart-coefficient extraction that the eventual `Subsingleton` proof
performs yields a pair of functions `f, g : ℂ → ℂ` related, on the
overlap `w ≠ 0`, by the transformation

  `g w = - f w⁻¹ / w^2`,

where `f` is the north-chart coefficient and `g` is the south-chart
coefficient. Holomorphicity of the global 1-form at `∞ ∈ RiemannSphere`
forces `g` to be (continuously) defined at `w = 0`.

This file extracts the analytic consequence the Liouville step of the
`Subsingleton` proof actually uses:

* `tendsto_zero_cocompact_of_southChart_continuous` —
  if `g w = -f w⁻¹ / w^2` on `w ≠ 0` and `g` is continuous at `0`,
  then `f` tends to `0` along `Filter.cocompact ℂ`.

This is exactly the `hb` hypothesis in
`RiemannSphereGenus.Liouville_holomorphic_form_chartN_coeff`, so combining
the two yields `f = 0` from a south-chart continuity hypothesis. The
chart-coefficient extraction map that produces the `g w = -f w⁻¹ / w^2`
relation lives downstream in the manifold-glue chase.

No `sorry`, no `axiom`. Purely analytic content; no manifold framework.
-/

set_option diagnostics.threshold 100

open Filter Topology Bornology

namespace JacobianChallenge

namespace RiemannSphere

/-- **South-chart-to-cocompact tendsto.** If two functions `f, g : ℂ → ℂ`
satisfy the south-chart transformation `g w = -f w⁻¹ / w^2` on `w ≠ 0`
and `g` is continuous at `0`, then `f` tends to `0` cocompactly.

Rewriting the relation as `f w⁻¹ = -w^2 · g w` for `w ≠ 0`, the right-hand
side tends to `-0 · g 0 = 0` as `w → 0` (continuity of `g`). Changing
variables via the inverse map (which sends `cocompact ℂ` back to `𝓝[≠] 0`)
yields the conclusion. -/
theorem tendsto_zero_cocompact_of_southChart_continuous
    {f g : ℂ → ℂ}
    (h_eq : ∀ w : ℂ, w ≠ 0 → g w = -f w⁻¹ / w ^ 2)
    (h_g : ContinuousAt g 0) :
    Tendsto f (cocompact ℂ) (𝓝 0) := by
  -- Switch from `cocompact ℂ` to `cobounded ℂ` via properness.
  rw [← Metric.cobounded_eq_cocompact (α := ℂ)]
  -- The complement of `{(0 : ℂ)}` is in `cobounded ℂ`.
  have hmem : {z : ℂ | z ≠ 0} ∈ (cobounded ℂ) := by
    have hbd : Bornology.IsBounded (({z : ℂ | z ≠ 0})ᶜ) := by
      have hc : ({z : ℂ | z ≠ 0})ᶜ = {(0 : ℂ)} := by ext z; simp
      rw [hc]; exact Bornology.isBounded_singleton
    rw [Bornology.isBounded_def] at hbd
    simpa using hbd
  -- On `{z ≠ 0}`, `f z = (fun w => f w⁻¹) z⁻¹`.
  have h_inv_inv :
      (fun w => f w⁻¹) ∘ Inv.inv =ᶠ[cobounded ℂ] f := by
    filter_upwards [hmem] with z hz
    change f z⁻¹⁻¹ = f z
    rw [inv_inv]
  refine (Filter.Tendsto.congr' h_inv_inv ?_)
  -- Compose `Inv.inv : cobounded ℂ → 𝓝[≠] 0` with the inner tendsto.
  refine (?_ : Tendsto (fun w => f w⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0)).comp
    tendsto_inv₀_cobounded'
  -- On `𝓝[≠] 0`, `f w⁻¹ = -w^2 * g w` by rearranging `h_eq`.
  have h_eq' :
      (fun w : ℂ => -w ^ 2 * g w) =ᶠ[𝓝[≠] (0 : ℂ)] (fun w => f w⁻¹) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    refine Filter.Eventually.of_forall (fun w (hw : w ≠ 0) => ?_)
    have hg : g w = -f w⁻¹ / w ^ 2 := h_eq w hw
    have hw2 : (w : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hw
    -- `-w^2 * g w = -w^2 * (-f w⁻¹ / w^2) = f w⁻¹`.
    rw [hg]
    field_simp
  refine Filter.Tendsto.congr' h_eq' ?_
  -- `Tendsto (fun w => -w^2 * g w) (𝓝[≠] 0) (𝓝 0)`.
  have h_w2 : Tendsto (fun w : ℂ => -w ^ 2) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have := ((continuous_neg.comp (continuous_pow 2)).tendsto (0 : ℂ))
    simpa using this
  have h_g_tendsto : Tendsto g (𝓝 (0 : ℂ)) (𝓝 (g 0)) := h_g
  have h_prod :
      Tendsto (fun w : ℂ => -w ^ 2 * g w) (𝓝 (0 : ℂ)) (𝓝 (0 * g 0)) :=
    h_w2.mul h_g_tendsto
  have h_prod' :
      Tendsto (fun w : ℂ => -w ^ 2 * g w) (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa using h_prod
  exact h_prod'.mono_left nhdsWithin_le_nhds

end RiemannSphere

end JacobianChallenge
