/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

set_option linter.unusedSectionVars false

/-! # `AnalyticOn ℂ` for parametric interval integrals

Wraps mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(parametric Fréchet derivative over `RCLike 𝕜`) at `𝕜 = ℂ` with
`DifferentiableOn.analyticOn` (Goursat) to give: a parametric integral
of a ℂ-differentiable-in-`z` integrand with locally-dominated
ℂ-derivative is `AnalyticOn ℂ` on any open parameter set.

This is the foundation atom for the **holomorphic parametric integral
arc** that closes `ChartLocalPrimitiveSmoothExt` (i.e., `h_smooth_b`
of item 14) without needing the ℂ→ℝ scalar-restriction bridge — the
parametric integral is taken at the ℂ-level, and the analyticity of
the result follows from per-point complex differentiability via
Goursat.

## What this file ships

* `analyticOn_intervalIntegral_param` — abstract: for `f : ℂ → ℝ → ℂ`
  with per-point ℂ-derivative `f'` and local domination bounds on
  `f'`, the parameter map `z ↦ ∫ t in a..b, f z t` is `AnalyticOn ℂ`
  on any open set `S`.

The hypotheses are bundled into one lemma; downstream callers
(e.g., the chartLocalPrimitive specialization) supply concrete bounds
based on compactness of `[a, b]` and continuity of `f, f'` in `(z, t)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology MeasureTheory
open MeasureTheory Set Filter

/-- **`AnalyticOn ℂ` for a parametric interval integral.**

For `f : ℂ → ℝ → ℂ` with:
* per-point ℂ-derivative `HasDerivAt (fun z' => f z' t) (f' z t) z`
  for every `z ∈ S`, ae `t ∈ Set.uIoc a b`;
* local ε-ball domination: at each `z₀ ∈ S`, an ε-ball `B ⊆ S` with
  `‖f' z t‖ ≤ bound t` for all `z ∈ B`, ae `t`, with `bound` interval-
  integrable;
* basic measurability and integrability of `f` and `f'` on `S × [a, b]`,

the parameter map `z ↦ ∫ t in a..b, f z t` is `AnalyticOn ℂ` on `S`
(open).

Proof: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
gives `HasDerivAt` at each `z₀ ∈ S`. Pointwise → `DifferentiableOn ℂ`
on `S`. Goursat (`DifferentiableOn.analyticOn`) on open `S` closes. -/
theorem analyticOn_intervalIntegral_param
    {f : ℂ → ℝ → ℂ} {f' : ℂ → ℝ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    {a b : ℝ}
    (h_meas_F : ∀ᶠ z in Filter.principal S,
      AEStronglyMeasurable (f z) (volume.restrict (Set.uIoc a b)))
    (h_int_F : ∀ z ∈ S, IntervalIntegrable (f z) volume a b)
    (h_meas_F' : ∀ z ∈ S,
      AEStronglyMeasurable (f' z) (volume.restrict (Set.uIoc a b)))
    (h_local_bound : ∀ z₀ ∈ S, ∃ ε > 0, Metric.ball z₀ ε ⊆ S ∧
      ∃ bound : ℝ → ℝ, IntervalIntegrable bound volume a b ∧
        ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
          ∀ z ∈ Metric.ball z₀ ε, ‖f' z t‖ ≤ bound t)
    (h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      ∀ z ∈ S, HasDerivAt (fun z' => f z' t) (f' z t) z) :
    AnalyticOn ℂ (fun z => ∫ t in a..b, f z t) S := by
  -- Step 1: pointwise HasDerivAt at each z₀ ∈ S via mathlib.
  have h_diffAt : ∀ z₀ ∈ S, DifferentiableAt ℂ (fun z => ∫ t in a..b, f z t) z₀ := by
    intro z₀ hz₀
    obtain ⟨ε, hε_pos, h_ball_sub, bound, h_bound_int, h_bound⟩ :=
      h_local_bound z₀ hz₀
    -- Apply mathlib's parametric derivative theorem on the ε-ball.
    have h_ball_nhds : Metric.ball z₀ ε ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hε_pos
    have h_S_nhds : S ∈ 𝓝 z₀ := hS.mem_nhds hz₀
    have h_meas_F_nhds : ∀ᶠ z in 𝓝 z₀,
        AEStronglyMeasurable (f z) (volume.restrict (Set.uIoc a b)) := by
      have := h_meas_F
      rw [Filter.eventually_principal] at this
      exact Filter.eventually_of_mem h_S_nhds this
    have h_diff_on_ball : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
        ∀ z ∈ Metric.ball z₀ ε, HasDerivAt (fun z' => f z' t) (f' z t) z := by
      filter_upwards [h_diff] with t ht ht_in z hz
      exact ht ht_in z (h_ball_sub hz)
    -- mathlib's hasDerivAt_integral_of_dominated_loc_of_deriv_le.
    have h_derivAt := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := f) (F' := f') (x₀ := z₀) (s := Metric.ball z₀ ε)
      (a := a) (b := b) (bound := bound)
      h_ball_nhds h_meas_F_nhds (h_int_F z₀ hz₀) (h_meas_F' z₀ hz₀)
      h_bound h_bound_int h_diff_on_ball
    exact h_derivAt.2.differentiableAt
  -- Step 2: DifferentiableAt-pointwise ⇒ DifferentiableOn on S.
  have h_diff_on : DifferentiableOn ℂ (fun z => ∫ t in a..b, f z t) S :=
    fun z hz => (h_diffAt z hz).differentiableWithinAt
  -- Step 3: Goursat on open S.
  exact h_diff_on.analyticOn hS

end
