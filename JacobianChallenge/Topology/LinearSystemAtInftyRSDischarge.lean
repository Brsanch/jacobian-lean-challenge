/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.PolynomialLiouville
import JacobianChallenge.Topology.LinearSystemGermDeltaPFiniteDimRSFromInputs
import Mathlib.Analysis.Meromorphic.NormalForm

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Discharge of `LinearSystemAtInftyRS_BoundedBySimplePoleSpan`

This file discharges the named hypothesis
`LinearSystemAtInftyRS_BoundedBySimplePoleSpan` (defined in
`Topology/LinearSystemGermDeltaPFiniteDimRSFromInputs.lean`) by proving
the polynomial-growth Liouville bound at `∞ ∈ RS`:

  `linearSystemGermDeltaP (∞ : RS) ≤ Submodule.span ℂ {1, RSSimplePoleGerm}`.

## Strategy

For a germ `φ ∈ linearSystemGermDeltaP (∞ : RS)` with representative
`f : MMer RS`:

1. **Affine-chart restriction.** Define `f_aff : ℂ → ℂ := f.toFun ∘ some`
   (the north chart of RS misses ∞ and identifies `ℂ` with the affine
   part). Manifold-level order conditions push to chart-side:
   - `mmeromorphicOrderAt f.toFun (some z) ≥ 0` for every `z : ℂ`
     translates to `meromorphicOrderAt f_aff z ≥ 0`.
   - `mmeromorphicOrderAt f.toFun (∞ : RS) ≥ -1` translates to a linear
     growth bound on `f_aff` at infinity.

2. **Entire normal-form representative.** Define `F := toMeromorphicNFOn
   f_aff Set.univ`. By `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`,
   `F` is analytic on all of ℂ (the normal-form conversion preserves
   meromorphic order, and order ≥ 0 everywhere ⇒ analytic). So `F` is
   entire, and `F =ᶠ[𝓝[≠] z] f_aff` at every `z : ℂ`.

3. **Linear growth bound.** The chart-S meromorphic order condition at 0
   gives `‖F z‖ ≤ C ‖z‖` for `‖z‖` sufficiently large.

4. **Polynomial Liouville.** `polynomial_liouville_linear` applied to `F`
   yields `F z = F 0 + (deriv F 0) z`.

5. **Germ identity.** With `a := F 0`, `b := deriv F 0`, prove
   `f.toFun =ᶠ[𝓝[≠] y] (fun x => a + b · RSSimplePole x)` at every
   `y : RS`. The two-chart case analysis:
   - At finite `y = some z₀`: a punctured nhd is `some '' (V \ {z₀})`.
     On this set, `f.toFun (some w) = f_aff w =ᶠ[𝓝[≠] z₀] F w = a + b w`
     `= a + b · RSSimplePole (some w)`.
   - At `y = ∞`: a punctured nhd is `chartS.symm '' (W \ {0})`. On this,
     `f.toFun (chartS.symm w) = f.toFun (some w⁻¹) = F(w⁻¹) = a + b w⁻¹`
     `= a + b · RSSimplePole (chartS.symm w)`.

6. **Conclusion.** As germs, `mk f = a • 1 + b • RSSimplePoleGerm`, so
   `φ ∈ Submodule.span ℂ {1, RSSimplePoleGerm}`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff OnePoint
open Filter Set Function

namespace JacobianChallenge.MeromorphicFunctionField

open JacobianChallenge

/-! ## Step 1: Affine-chart restriction

The function `affineChartFun f := f.toFun ∘ some`. The manifold chart at
`some z : RS` is `chartN`, with `chartN.symm w = some w` and
`chartN (some z) = z`. So the manifold meromorphic order matches the
chart-side order: `mmeromorphicOrderAt f.toFun (some z) = meromorphicOrderAt
(f.toFun ∘ some) z`. -/

/-- The affine-chart restriction of a meromorphic function on the Riemann
sphere: `affineChartFun f z := f.toFun (some z)`. -/
def affineChartFun (f : MMer RiemannSphere) : ℂ → ℂ :=
  fun z => f.toFun ((z : RiemannSphere))

/-- The affine-chart restriction agrees with the chart pullback
`f.toFun ∘ chartN.symm`. -/
lemma affineChartFun_eq_chartN_pullback (f : MMer RiemannSphere) :
    affineChartFun f = f.toFun ∘ RiemannSphere.chartN.symm := by
  funext w
  show f.toFun ((w : RiemannSphere)) = f.toFun (RiemannSphere.chartN.symm w)
  rw [RiemannSphere.chartN_symm_apply]

/-- `mmeromorphicOrderAt f.toFun (some z) = meromorphicOrderAt
(affineChartFun f) z`. The manifold-side and chart-side orders agree at
finite points. -/
lemma mmero_orderAt_coe_eq_affineChartFun
    (f : MMer RiemannSphere) (z : ℂ) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun ((z : RiemannSphere))
      = meromorphicOrderAt (affineChartFun f) z := by
  show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
      ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere)))
    = meromorphicOrderAt (affineChartFun f) z
  have h_chart : (chartAt ℂ ((z : RiemannSphere))
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartN := rfl
  rw [h_chart, RiemannSphere.chartN_apply_coe, ← affineChartFun_eq_chartN_pullback]

/-- The affine-chart function is meromorphic everywhere on `ℂ`. -/
lemma affineChartFun_meromorphicOn (f : MMer RiemannSphere) :
    MeromorphicOn (affineChartFun f) Set.univ := by
  intro z _
  -- `affineChartFun f` is meromorphic at `z` iff the chart pullback is.
  have h_mmero : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun ((z : RiemannSphere)) :=
    f.mmero ((z : RiemannSphere)) trivial
  -- `MMeromorphicAt I f x` is by definition `MeromorphicAt (f ∘ chart.symm) (chart x)`.
  have h_chart_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ ((z : RiemannSphere))).symm)
      ((chartAt ℂ ((z : RiemannSphere))) ((z : RiemannSphere))) := h_mmero
  have h_chart : (chartAt ℂ ((z : RiemannSphere))
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartN := rfl
  rw [h_chart, RiemannSphere.chartN_apply_coe] at h_chart_mero
  rwa [affineChartFun_eq_chartN_pullback]

/-- From `IsBoundedByDeltaPGerm ∞`: at every finite `z`, the affine-chart
function has order `≥ 0`. -/
lemma order_affineChartFun_nonneg_of_bounded
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f))
    (z : ℂ) :
    0 ≤ meromorphicOrderAt (affineChartFun f) z := by
  -- `h.2 : ∀ y, y ≠ ∞ → 0 ≤ mmeromorphicOrderAt _ f.toFun y`.
  have h_off : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun ((z : RiemannSphere)) :=
    h.2 ((z : RiemannSphere)) (OnePoint.coe_ne_infty z)
  rwa [mmero_orderAt_coe_eq_affineChartFun] at h_off

/-! ## Step 2: Entire normal-form representative

Using mathlib's `toMeromorphicNFOn`, build an analytic representative
`entireRep f` of `affineChartFun f` that agrees with `affineChartFun f`
on punctured nhds. The "order ≥ 0 everywhere" condition gives that the
normal-form rep is analytic on all of ℂ. -/

/-- The entire representative: convert `affineChartFun f` to normal form
on `Set.univ`. By preservation of order plus the order-≥-0 hypothesis,
the result is analytic on all of ℂ. -/
def entireRep (f : MMer RiemannSphere) : ℂ → ℂ :=
  toMeromorphicNFOn (affineChartFun f) Set.univ

/-- `entireRep f` agrees with `affineChartFun f` on a punctured nhd of
every `z : ℂ`. -/
lemma entireRep_eventuallyEq_affineChartFun
    (f : MMer RiemannSphere) (z : ℂ) :
    entireRep f =ᶠ[𝓝[≠] z] affineChartFun f := by
  apply MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
  · exact affineChartFun_meromorphicOn f
  · trivial

/-- `entireRep f` is in normal form on all of `ℂ`. -/
lemma entireRep_meromorphicNFOn (f : MMer RiemannSphere) :
    MeromorphicNFOn (entireRep f) Set.univ :=
  meromorphicNFOn_toMeromorphicNFOn (affineChartFun f) Set.univ

/-- Under the order-≥-0 hypothesis, `entireRep f` is analytic on all of `ℂ`. -/
lemma entireRep_analyticOnNhd
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    AnalyticOnNhd ℂ (entireRep f) Set.univ := by
  -- Use `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`.
  rw [← (entireRep_meromorphicNFOn f).divisor_nonneg_iff_analyticOnNhd]
  -- Show `0 ≤ MeromorphicOn.divisor (entireRep f) Set.univ`.
  -- The divisor of `entireRep` equals the divisor of `affineChartFun f`
  -- since `meromorphicOrderAt_toMeromorphicNFOn` preserves order.
  intro z
  by_cases hz : z ∈ Set.univ
  · -- `z ∈ Set.univ` is trivially true.
    have h_mero_ent : MeromorphicOn (entireRep f) Set.univ :=
      (entireRep_meromorphicNFOn f).meromorphicOn
    have h_div : (MeromorphicOn.divisor (entireRep f) Set.univ : ℂ → ℤ) z
        = (meromorphicOrderAt (entireRep f) z).untop₀ := by
      simp [MeromorphicOn.divisor_apply h_mero_ent hz]
    have h_ord_ent : meromorphicOrderAt (entireRep f) z
        = meromorphicOrderAt (affineChartFun f) z :=
      meromorphicOrderAt_toMeromorphicNFOn (affineChartFun_meromorphicOn f) hz
    have h_ord_nn : 0 ≤ meromorphicOrderAt (affineChartFun f) z :=
      order_affineChartFun_nonneg_of_bounded f h z
    show (0 : ℤ) ≤ (MeromorphicOn.divisor (entireRep f) Set.univ : ℂ → ℤ) z
    rw [h_div, h_ord_ent]
    exact WithTop.untop₀_nonneg.mpr h_ord_nn
  · exact absurd hz (not_not.mpr (Set.mem_univ z))

/-- `entireRep f` is differentiable on all of `ℂ`. -/
lemma entireRep_differentiable
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    Differentiable ℂ (entireRep f) := by
  intro z
  exact ((entireRep_analyticOnNhd f h) z (Set.mem_univ _)).differentiableAt

/-! ## Step 3: Linear growth bound

The hypothesis `IsBoundedByDeltaPGerm ∞ (mk f)` includes
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun (∞ : RS) ≥ -1`. Unfolding via the
south chart `chartS`, this becomes
`meromorphicOrderAt (f.toFun ∘ chartS.symm) 0 ≥ -1` (since
`chartS ∞ = 0`).

Hence `id * (f.toFun ∘ chartS.symm)` has meromorphic order `≥ 0` at 0
(order is additive under multiplication). By
`tendsto_nhds_of_meromorphicOrderAt_nonneg`, the product converges to a
finite limit at 0, hence is bounded near 0.

Translating to `affineChartFun f` via the chart-S substitution
`chartS.symm w = some w⁻¹` (for `w ≠ 0`): there exist `C` and `R₀ > 0`
such that `‖affineChartFun f z‖ ≤ C * ‖z‖` for `‖z‖ ≥ R₀`.

Combined with the punctured-nhd identification between `entireRep f` and
`affineChartFun f`, plus continuity of `entireRep f`, this gives the
same growth bound for `entireRep f`. -/

/-- The south-chart pullback `f.toFun ∘ chartS.symm` is meromorphic at 0. -/
lemma fSouthChart_meromorphicAt (f : MMer RiemannSphere) :
    MeromorphicAt (f.toFun ∘ RiemannSphere.chartS.symm) 0 := by
  have h_mmero : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun (∞ : RiemannSphere) :=
    f.mmero (∞ : RiemannSphere) trivial
  -- `MMeromorphicAt` unfolds to `MeromorphicAt (f ∘ chartAt.symm) (chartAt x)`.
  have h_chart_mero :
      MeromorphicAt (f.toFun ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
        ((chartAt ℂ (∞ : RiemannSphere)) ∞) := h_mmero
  have h_chart : (chartAt ℂ (∞ : RiemannSphere)
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartS := rfl
  rw [h_chart, RiemannSphere.chartS_apply_infty] at h_chart_mero
  exact h_chart_mero

/-- The south-chart order: `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun ∞ =
meromorphicOrderAt (f.toFun ∘ chartS.symm) 0`. -/
lemma mmero_orderAt_infty_eq_southChart
    (f : MMer RiemannSphere) :
    mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun (∞ : RiemannSphere)
      = meromorphicOrderAt (f.toFun ∘ RiemannSphere.chartS.symm) 0 := by
  show meromorphicOrderAt (f.toFun ∘ (chartAt ℂ (∞ : RiemannSphere)).symm)
      ((chartAt ℂ (∞ : RiemannSphere)) ∞)
    = meromorphicOrderAt (f.toFun ∘ RiemannSphere.chartS.symm) 0
  have h_chart : (chartAt ℂ (∞ : RiemannSphere)
        : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartS := rfl
  rw [h_chart, RiemannSphere.chartS_apply_infty]

/-- The "scaled south-chart pullback" `w ↦ w * (f.toFun ∘ chartS.symm)(w)`
has meromorphic order `≥ 0` at 0, by additivity (order of `id` is 1,
order of `f.toFun ∘ chartS.symm` is `≥ -1`). -/
lemma id_mul_southChart_orderAt_nonneg
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    0 ≤ meromorphicOrderAt
      (fun w : ℂ => w * (f.toFun ∘ RiemannSphere.chartS.symm) w) 0 := by
  have h_mero_h : MeromorphicAt (f.toFun ∘ RiemannSphere.chartS.symm) 0 :=
    fSouthChart_meromorphicAt f
  have h_mero_id : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
  -- `meromorphicOrderAt (id * h) 0 = meromorphicOrderAt id 0 + meromorphicOrderAt h 0`.
  have h_eq_idmul : (fun w : ℂ => w * (f.toFun ∘ RiemannSphere.chartS.symm) w)
      = (id : ℂ → ℂ) * (f.toFun ∘ RiemannSphere.chartS.symm) := by
    funext w; show w * _ = id w * _; rfl
  rw [h_eq_idmul, meromorphicOrderAt_mul h_mero_id h_mero_h,
      meromorphicOrderAt_id]
  -- Goal: `(0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt (f.toFun ∘ chartS.symm) 0`.
  have h_h_ge : ((-1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (f.toFun ∘ RiemannSphere.chartS.symm) 0 := by
    rw [← mmero_orderAt_infty_eq_southChart]
    exact h.1
  -- Case-split on the order: either `⊤` or finite `(n : ℤ)` with `n ≥ -1`.
  set ord := meromorphicOrderAt (f.toFun ∘ RiemannSphere.chartS.symm) 0 with hord_def
  rcases eq_or_ne ord ⊤ with h_top | h_ne_top
  · -- `ord = ⊤`. Then `1 + ⊤ = ⊤ ≥ 0`.
    rw [h_top]
    simp
  · -- `ord = (n : ℤ)` for some `n ≥ -1`.
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
    rw [← hn]
    -- h_h_ge : ((-1 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ).
    rw [← hn] at h_h_ge
    have h_n_ge : (-1 : ℤ) ≤ n := by exact_mod_cast h_h_ge
    -- Goal: `(0 : WithTop ℤ) ≤ 1 + ((n : ℤ) : WithTop ℤ)`.
    have h_combine : (1 : WithTop ℤ) + ((n : ℤ) : WithTop ℤ) = ((1 + n : ℤ) : WithTop ℤ) := by
      push_cast
      rfl
    rw [h_combine]
    -- Goal: `(0 : WithTop ℤ) ≤ ((1 + n : ℤ) : WithTop ℤ)`.
    have : (0 : ℤ) ≤ 1 + n := by linarith
    exact_mod_cast this

/-- Existence of a punctured-nhd bound: `‖w * h(w)‖ ≤ M` for `w` in a
punctured nhd of 0, where `h := f.toFun ∘ chartS.symm`. -/
lemma exists_bound_id_mul_southChart
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    ∃ M : ℝ, ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖w * (f.toFun ∘ RiemannSphere.chartS.symm) w‖ ≤ M := by
  have h_mero : MeromorphicAt
      (fun w : ℂ => w * (f.toFun ∘ RiemannSphere.chartS.symm) w) 0 := by
    have h_mero_h : MeromorphicAt (f.toFun ∘ RiemannSphere.chartS.symm) 0 :=
      fSouthChart_meromorphicAt f
    have h_mero_id : MeromorphicAt (id : ℂ → ℂ) 0 := analyticAt_id.meromorphicAt
    have h_eq : (fun w : ℂ => w * (f.toFun ∘ RiemannSphere.chartS.symm) w)
        = (id : ℂ → ℂ) * (f.toFun ∘ RiemannSphere.chartS.symm) := by
      funext w; show w * _ = id w * _; rfl
    rw [h_eq]
    exact h_mero_id.mul h_mero_h
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg h_mero
    (id_mul_southChart_orderAt_nonneg f h)
  -- `Tendsto _ (𝓝[≠] 0) (𝓝 c)`. Then for any ε > 0, eventually `‖_ - c‖ < ε`.
  refine ⟨‖c‖ + 1, ?_⟩
  have h_norm_tendsto : Tendsto
      (fun w => ‖w * (f.toFun ∘ RiemannSphere.chartS.symm) w‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖c‖) :=
    hc.norm
  have h_eventually : ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖w * (f.toFun ∘ RiemannSphere.chartS.symm) w‖ < ‖c‖ + 1 := by
    rw [Metric.tendsto_nhds] at h_norm_tendsto
    have := h_norm_tendsto 1 (by norm_num)
    filter_upwards [this] with w hw
    rw [Real.dist_eq] at hw
    linarith [abs_lt.mp hw |>.2]
  exact h_eventually.mono (fun w hw => le_of_lt hw)

/-! ### Translation to a growth bound on `affineChartFun f`

Substituting `w = z⁻¹` (so `chartS.symm w = some w⁻¹ = some z` for
`w ≠ 0`), the bound `‖w · (f.toFun ∘ chartS.symm) w‖ ≤ M` for `w` in a
punctured nhd of 0 becomes `‖affineChartFun f z‖ ≤ M · ‖z‖` for `‖z‖`
large enough. -/

/-- Existence of `M ≥ 0` and `R₀ > 0` such that
`‖affineChartFun f z‖ ≤ M · ‖z‖` for `‖z‖ ≥ R₀`. -/
lemma exists_growth_bound_affineChartFun
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    ∃ M R₀ : ℝ, 0 ≤ M ∧ 0 < R₀ ∧
      ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖affineChartFun f z‖ ≤ M * ‖z‖ := by
  obtain ⟨M, hM_evt⟩ := exists_bound_id_mul_southChart f h
  -- Unpack `∀ᶠ w in 𝓝[≠] 0` to `∃ δ > 0, ∀ w, ‖w‖ < δ → w ≠ 0 → ...`.
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hM_evt
  obtain ⟨δ, hδ_pos, hM⟩ := hM_evt
  -- `hM : ∀ w, dist w 0 < δ → w ∈ {0}ᶜ → ‖w * _‖ ≤ M`.
  -- Take `R₀ := 1/δ + 1` and `M' := max M 0` (to guarantee `0 ≤ M'`).
  refine ⟨max M 0, 1/δ + 1, le_max_right _ _, by positivity, ?_⟩
  intro z hz
  -- `1/δ + 1 ≤ ‖z‖` ⇒ `‖z‖ > 1/δ > 0`, so `z ≠ 0` and `‖z⁻¹‖ = 1/‖z‖ < δ`.
  have h_one_div_pos : 0 < 1/δ := one_div_pos.mpr hδ_pos
  have hz_pos : 0 < ‖z‖ := by linarith
  have hz_ne_zero : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hz_pos)
  set w : ℂ := z⁻¹ with hw_def
  have hw_ne_zero : w ≠ 0 := inv_ne_zero hz_ne_zero
  have hw_norm : ‖w‖ = ‖z‖⁻¹ := by rw [hw_def, norm_inv]
  have hw_lt : ‖w‖ < δ := by
    rw [hw_norm, inv_eq_one_div, div_lt_iff₀ hz_pos, mul_comm]
    -- Goal: 1 < ‖z‖ * δ.
    -- We have `1/δ + 1 ≤ ‖z‖`, so `‖z‖ * δ ≥ (1/δ + 1) * δ = 1 + δ > 1`.
    have h_step : (1/δ + 1) * δ ≤ ‖z‖ * δ :=
      mul_le_mul_of_nonneg_right hz hδ_pos.le
    have h_simplify : (1/δ + 1) * δ = 1 + δ := by field_simp
    linarith
  have h_dist : dist w 0 < δ := by simp [dist_eq_norm, hw_lt]
  have h_compl : w ∈ ({0} : Set ℂ)ᶜ := by
    simp [Set.mem_compl_iff, hw_ne_zero]
  have h_bd := hM (y := w) h_dist h_compl
  -- `h_bd : ‖w * (f.toFun ∘ chartS.symm) w‖ ≤ M`.
  -- `(f.toFun ∘ chartS.symm) w = f.toFun (chartS.symm w) = f.toFun (some w⁻¹)`
  -- `                          = f.toFun (some z) = affineChartFun f z`.
  have h_simp : (f.toFun ∘ RiemannSphere.chartS.symm) w = affineChartFun f z := by
    show f.toFun (RiemannSphere.chartS.symm w) = f.toFun ((z : RiemannSphere))
    rw [RiemannSphere.chartS_symm_apply_of_ne hw_ne_zero]
    congr 1
    show ((w⁻¹ : ℂ) : RiemannSphere) = ((z : ℂ) : RiemannSphere)
    rw [hw_def, inv_inv]
  rw [h_simp] at h_bd
  -- `h_bd : ‖w * affineChartFun f z‖ ≤ M`.
  rw [norm_mul, hw_norm] at h_bd
  -- h_bd : ‖z‖⁻¹ * ‖affineChartFun f z‖ ≤ M
  have h_z_ne : (‖z‖ : ℝ) ≠ 0 := ne_of_gt hz_pos
  -- Multiply both sides by ‖z‖ (positive): `‖affineChartFun f z‖ ≤ M * ‖z‖`.
  have h_mul : ‖z‖ * (‖z‖⁻¹ * ‖affineChartFun f z‖) ≤ ‖z‖ * M :=
    mul_le_mul_of_nonneg_left h_bd hz_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ h_z_ne, one_mul] at h_mul
  have h_final : ‖affineChartFun f z‖ ≤ M * ‖z‖ := by linarith
  -- Now lift `M` to `max M 0`:
  exact h_final.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz_pos.le)

/-! ### Lift growth bound from `affineChartFun f` to `entireRep f`

`entireRep f` agrees with `affineChartFun f` on a punctured nhd of every
`z`. So the growth bound `‖affineChartFun f w‖ ≤ M ‖w‖` for `‖w‖ ≥ R₀`
transfers to `entireRep f` on a punctured nhd of any `z` with `‖z‖ > R₀`.
By continuity of `entireRep f`, the bound extends to `z` itself. -/

/-- Existence of growth bound for `entireRep f`. -/
lemma exists_growth_bound_entireRep
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    ∃ M R₀ : ℝ, 0 ≤ M ∧ 0 < R₀ ∧
      ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖entireRep f z‖ ≤ M * ‖z‖ := by
  obtain ⟨M, R₀, hM_nn, hR₀_pos, hM⟩ := exists_growth_bound_affineChartFun f h
  refine ⟨M, R₀ + 1, hM_nn, by linarith, ?_⟩
  intro z hz
  -- On a punctured nhd of z (with ‖·‖ ≥ R₀), `‖entireRep f w‖ ≤ M ‖w‖`.
  have h_evt_bound : ∀ᶠ w in 𝓝[≠] z, ‖entireRep f w‖ ≤ M * ‖w‖ := by
    have h_evt_eq := entireRep_eventuallyEq_affineChartFun f z
    have h_R₀_lt : R₀ < ‖z‖ := by linarith
    have h_open : IsOpen { w : ℂ | R₀ < ‖w‖ } :=
      isOpen_lt continuous_const continuous_norm
    have h_z_mem : z ∈ { w : ℂ | R₀ < ‖w‖ } := h_R₀_lt
    have h_norm_evt : ∀ᶠ w in 𝓝 z, R₀ ≤ ‖w‖ := by
      filter_upwards [h_open.mem_nhds h_z_mem] with w hw using hw.le
    have h_norm_evt' : ∀ᶠ w in 𝓝[≠] z, R₀ ≤ ‖w‖ :=
      h_norm_evt.filter_mono nhdsWithin_le_nhds
    filter_upwards [h_evt_eq, h_norm_evt'] with w hw_eq hw_norm
    rw [hw_eq]
    exact hM w hw_norm
  -- Take limit `w → z`: both sides continuous, so inequality extends.
  have h_cont_F : Continuous (entireRep f) :=
    (entireRep_differentiable f h).continuous
  have h_tendsto_F : Tendsto (fun w => ‖entireRep f w‖)
      (𝓝[≠] z) (𝓝 ‖entireRep f z‖) :=
    (h_cont_F.continuousAt.tendsto.norm).mono_left nhdsWithin_le_nhds
  have h_tendsto_M : Tendsto (fun w : ℂ => M * ‖w‖)
      (𝓝[≠] z) (𝓝 (M * ‖z‖)) := by
    have h_norm : Tendsto (fun w : ℂ => ‖w‖) (𝓝[≠] z) (𝓝 ‖z‖) :=
      (continuous_norm.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    exact h_norm.const_mul M
  exact le_of_tendsto_of_tendsto h_tendsto_F h_tendsto_M h_evt_bound

/-! ## Step 4: Apply polynomial Liouville

Combining: `entireRep f` is differentiable on ℂ AND satisfies linear
growth at infinity. By `polynomial_liouville_linear`,
`entireRep f w = entireRep f 0 + (deriv (entireRep f) 0) * w` for all `w`. -/

/-- The constant term of the polynomial Liouville representation. -/
def entireRepCoeffA (f : MMer RiemannSphere) : ℂ := entireRep f 0

/-- The linear coefficient of the polynomial Liouville representation. -/
def entireRepCoeffB (f : MMer RiemannSphere) : ℂ := deriv (entireRep f) 0

/-- **Polynomial Liouville for `entireRep f`**: `entireRep f w = a + b · w`
for all `w : ℂ`, where `a, b` are the coefficients defined above. -/
theorem entireRep_eq_affine
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    ∀ w : ℂ, entireRep f w
      = entireRepCoeffA f + entireRepCoeffB f * w := by
  obtain ⟨M, R₀, hM_nn, hR₀_pos, hM⟩ := exists_growth_bound_entireRep f h
  intro w
  -- Apply `Complex.polynomial_liouville_linear`.
  -- Hypothesis: ∀ z, R₀ ≤ ‖z‖ → ‖entireRep f z‖ ≤ M * ‖z‖.
  exact JacobianChallenge.Complex.polynomial_liouville_linear
    (entireRep_differentiable f h) hM_nn hR₀_pos.le hM w

/-! ## Step 5: Germ identity via the identity theorem

By Step 4, `affineChartFun f =ᶠ[𝓝[≠] 0] (fun w => a + b · w)` (composing
Step 2 with the polynomial identity). Lifting to RS-side via the chart
`chartN`, we get `f.toFun =ᶠ[𝓝[≠] (some 0)] (fun x => a + b · RSSimplePole x)`.

By the identity theorem for meromorphic functions on a connected
complex 1-manifold (`mmeromorphicOrderAt_ne_top_forall`), this single-
point EvEq propagates: the function `f - (a + b · RSSimplePole)` has
infinite meromorphic order at every point of RS, hence is the zero
germ. -/

/-- The polynomial-side `MMer` representative
`g := MMer.const a + b • RSSimplePoleMMer`. -/
def polyMMer (f : MMer RiemannSphere) : MMer RiemannSphere :=
  MMer.const (entireRepCoeffA f) + entireRepCoeffB f • RSSimplePoleMMer

/-- The polynomial `MMer.toFun` evaluated. -/
lemma polyMMer_toFun (f : MMer RiemannSphere) (x : RiemannSphere) :
    (polyMMer f).toFun x
      = entireRepCoeffA f + entireRepCoeffB f * RSSimplePole x := by
  show (MMer.const (entireRepCoeffA f)).toFun x
        + (entireRepCoeffB f • RSSimplePoleMMer).toFun x
      = entireRepCoeffA f + entireRepCoeffB f * RSSimplePole x
  simp only [MMer.const_toFun, MMer.smul_toFun, Pi.smul_apply,
    RSSimplePoleMMer_toFun, smul_eq_mul]

/-- **One-point germ identity**: at `some 0`, the function `f.toFun` and
the polynomial `polyMMer f.toFun` agree on a punctured nhd. -/
lemma f_eq_polyMMer_punctured_at_zero
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    f.toFun =ᶠ[𝓝[≠] ((0 : ℂ) : RiemannSphere)] (polyMMer f).toFun := by
  -- At the manifold level, a punctured nhd of `some 0` is `chartN.symm '' (V \ {0})`
  -- for `V` a nhd of `0` in ℂ. So we work via chart-N.
  -- Chart-N: `(z : RS) ↔ chartN z` (`some z ↔ z`).
  -- We need: ∀ᶠ x in 𝓝[≠] some 0, f.toFun x = (polyMMer f).toFun x.
  -- Via the chart, this transfers to: ∀ᶠ w in 𝓝[≠] 0 in ℂ, affineChartFun f w = polyMMer-on-some-w.
  -- `polyMMer f (some w) = a + b · RSSimplePole(some w) = a + b · w`.
  -- We have `affineChartFun f =ᶠ[𝓝[≠] 0] entireRep f` (Step 2)
  -- and `entireRep f w = a + b · w` everywhere (Step 4).
  -- So `affineChartFun f =ᶠ[𝓝[≠] 0] (fun w => a + b · w)`.
  have h_chart_evt : affineChartFun f
      =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun w : ℂ => entireRepCoeffA f + entireRepCoeffB f * w) := by
    have h_evt_eq := entireRep_eventuallyEq_affineChartFun f (0 : ℂ)
    -- h_evt_eq : entireRep f =ᶠ[𝓝[≠] 0] affineChartFun f
    have h_poly : ∀ w, entireRep f w
        = entireRepCoeffA f + entireRepCoeffB f * w :=
      entireRep_eq_affine f h
    -- Combine via congr.
    filter_upwards [h_evt_eq] with w hw
    rw [← hw, h_poly]
  -- Now transport from chart-N coordinates to RS.
  -- Punctured nhd of `some 0` in RS comes from chartN.symm of punctured nhd of 0.
  -- chartN is a homeomorphism on its source `{∞}ᶜ`, so the pullback `(some : ℂ → RS)`
  -- has continuous inverse on `{some w : w ∈ ℂ}`.
  -- We use `chartSymm_tendsto_nhdsNE` from the repo to push EvEq through the chart.
  have h_tendsto := JacobianChallenge.MeromorphicNonzero.chartSymm_tendsto_nhdsNE
    (((0 : ℂ) : RiemannSphere))
  -- h_tendsto : Tendsto (chartAt ℂ ...).symm (𝓝[≠] (chartAt ... (some 0))) (𝓝[≠] (some 0))
  -- chartAt ℂ (some 0) = chartN, chartN (some 0) = 0.
  -- So h_tendsto : Tendsto chartN.symm (𝓝[≠] 0) (𝓝[≠] (some 0))
  have h_chart_apply : (chartAt ℂ ((0 : ℂ) : RiemannSphere))
        ((0 : ℂ) : RiemannSphere) = (0 : ℂ) := by
    show RiemannSphere.chartN ((0 : ℂ) : RiemannSphere) = (0 : ℂ)
    exact RiemannSphere.chartN_apply_coe 0
  rw [h_chart_apply] at h_tendsto
  -- Push the chart-N evt through the inverse chart map.
  have h_push : (f.toFun ∘ (chartAt ℂ (((0 : ℂ) : RiemannSphere))).symm)
      =ᶠ[𝓝[≠] (0 : ℂ)]
        ((polyMMer f).toFun ∘ (chartAt ℂ (((0 : ℂ) : RiemannSphere))).symm) := by
    have h_chart_eq : (chartAt ℂ (((0 : ℂ) : RiemannSphere))
          : OpenPartialHomeomorph RiemannSphere ℂ) = RiemannSphere.chartN := rfl
    rw [h_chart_eq]
    filter_upwards [h_chart_evt] with w hw
    show f.toFun (RiemannSphere.chartN.symm w)
        = (polyMMer f).toFun (RiemannSphere.chartN.symm w)
    rw [RiemannSphere.chartN_symm_apply]
    -- LHS: f.toFun (some w) = affineChartFun f w. RHS: (polyMMer f).toFun (some w).
    -- affineChartFun f w = a + b w (from hw).
    -- (polyMMer f).toFun (some w) = a + b · RSSimplePole (some w) = a + b · w.
    show f.toFun ((w : RiemannSphere))
        = (polyMMer f).toFun ((w : RiemannSphere))
    have h_lhs : f.toFun ((w : RiemannSphere)) = affineChartFun f w := rfl
    rw [h_lhs, hw, polyMMer_toFun]
    rw [RSSimplePole_coe]
  -- Transport via `Tendsto.eventually` on the FORWARD chart direction.
  have h_chart_tendsto :=
    JacobianChallenge.MeromorphicNonzero.chart_tendsto_nhdsNE
      (((0 : ℂ) : RiemannSphere))
  rw [h_chart_apply] at h_chart_tendsto
  -- h_chart_tendsto : Tendsto (chartAt ℂ (some 0)) (𝓝[≠] some 0) (𝓝[≠] 0).
  have h_push_RS := h_chart_tendsto.eventually h_push
  -- h_push_RS : ∀ᶠ x in 𝓝[≠] some 0,
  --   (f.toFun ∘ chartN.symm) (chartN x) = ((polyMMer f).toFun ∘ chartN.symm) (chartN x)
  -- Simplify `chartN.symm ∘ chartN = id` on chart source.
  -- The punctured nhd of some 0 lies in chart-N source = {∞}ᶜ (since some 0 ≠ ∞).
  have h_source_nhd : (chartAt ℂ (((0 : ℂ) : RiemannSphere))).source ∈
      𝓝 (((0 : ℂ) : RiemannSphere)) := by
    apply (chartAt ℂ (((0 : ℂ) : RiemannSphere))).open_source.mem_nhds
    exact mem_chart_source ℂ _
  have h_source_evt : ∀ᶠ x in 𝓝[≠] (((0 : ℂ) : RiemannSphere)),
      x ∈ (chartAt ℂ (((0 : ℂ) : RiemannSphere))).source :=
    Filter.eventually_of_mem (nhdsWithin_le_nhds h_source_nhd) (fun _ h => h)
  filter_upwards [h_push_RS, h_source_evt] with x hx h_src
  -- `(chartAt ℂ ...).symm ((chartAt ℂ ...) x) = x` since `x ∈ source`.
  have h_left_inv : (chartAt ℂ (((0 : ℂ) : RiemannSphere))).symm
      ((chartAt ℂ (((0 : ℂ) : RiemannSphere))) x) = x :=
    (chartAt ℂ (((0 : ℂ) : RiemannSphere))).left_inv h_src
  show f.toFun x = (polyMMer f).toFun x
  have : f.toFun ((chartAt ℂ (((0 : ℂ) : RiemannSphere))).symm
      ((chartAt ℂ (((0 : ℂ) : RiemannSphere))) x))
        = (polyMMer f).toFun ((chartAt ℂ (((0 : ℂ) : RiemannSphere))).symm
            ((chartAt ℂ (((0 : ℂ) : RiemannSphere))) x)) := hx
  rwa [h_left_inv] at this

/-! ## Step 6: Identity theorem extends the germ equality to all of RS -/

/-- **Germ identity**: `mk f = mk (polyMMer f)` in `MeromorphicFunctionGerm RiemannSphere`. -/
theorem mk_f_eq_mk_polyMMer
    (f : MMer RiemannSphere)
    (h : IsBoundedByDeltaPGerm (∞ : RiemannSphere) (MeromorphicFunctionGerm.mk f)) :
    (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm RiemannSphere)
      = MeromorphicFunctionGerm.mk (polyMMer f) := by
  -- Consider `h_diff : MMer RS := f - polyMMer f`. Show `mk h_diff = 0`.
  -- Then `mk f = mk h_diff + mk polyMMer = 0 + mk polyMMer = mk polyMMer`.
  -- By the identity theorem, `mk h_diff = 0` follows from a single-point EvEq.
  have h_polyMMer_mmero : MMeromorphicOn 𝓘(ℂ, ℂ) (polyMMer f).toFun Set.univ :=
    (polyMMer f).mmero
  -- `(f - polyMMer f).toFun y =ᶠ[𝓝[≠] some 0] 0`.
  set hdiff : MMer RiemannSphere := f - polyMMer f with hdiff_def
  have h_one_point : hdiff.toFun =ᶠ[𝓝[≠] ((0 : ℂ) : RiemannSphere)] 0 := by
    have := f_eq_polyMMer_punctured_at_zero f h
    filter_upwards [this] with x hx
    show f.toFun x - (polyMMer f).toFun x = 0
    rw [hx, sub_self]
  -- By identity theorem, `mmeromorphicOrderAt hdiff.toFun y = ⊤` at every `y`.
  have h_order_at_zero : mmeromorphicOrderAt 𝓘(ℂ, ℂ) hdiff.toFun
      ((0 : ℂ) : RiemannSphere) = ⊤ := by
    rw [mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero hdiff.toFun hdiff.mmero]
    exact h_one_point
  -- Direct: show `mk hdiff = 0` using identity theorem, then derive `mk f = mk (polyMMer f)`.
  have h_all_top : ∀ y : RiemannSphere,
      mmeromorphicOrderAt 𝓘(ℂ, ℂ) hdiff.toFun y = ⊤ := by
    intro y
    by_contra h_not
    push_neg at h_not
    have h_exists : ∃ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) hdiff.toFun y ≠ ⊤ :=
      ⟨y, h_not⟩
    have h_all : ∀ y, mmeromorphicOrderAt 𝓘(ℂ, ℂ) hdiff.toFun y ≠ ⊤ :=
      mmeromorphicOrderAt_ne_top_forall hdiff.toFun hdiff.mmero h_exists
    exact h_all ((0 : ℂ) : RiemannSphere) h_order_at_zero
  -- mk hdiff = 0.
  have h_mk_diff_zero : (MeromorphicFunctionGerm.mk hdiff
      : MeromorphicFunctionGerm RiemannSphere) = 0 := by
    show (MeromorphicFunctionGerm.mk hdiff : MeromorphicFunctionGerm RiemannSphere)
        = MeromorphicFunctionGerm.mk (0 : MMer RiemannSphere)
    apply Quotient.sound
    intro y
    show hdiff.toFun =ᶠ[𝓝[≠] y] (0 : MMer RiemannSphere).toFun
    have h_zero_unfold : (0 : MMer RiemannSphere).toFun
        = (fun _ : RiemannSphere => (0 : ℂ)) := rfl
    rw [h_zero_unfold]
    exact (mmeromorphicOrderAt_eq_top_iff_eventually_eq_zero hdiff.toFun hdiff.mmero y).mp
      (h_all_top y)
  -- mk f - mk (polyMMer f) = mk hdiff = 0, hence mk f = mk (polyMMer f).
  have h_mk_sub : (MeromorphicFunctionGerm.mk f
        - MeromorphicFunctionGerm.mk (polyMMer f)
        : MeromorphicFunctionGerm RiemannSphere)
      = MeromorphicFunctionGerm.mk hdiff := by
    show (MeromorphicFunctionGerm.mk f
          - MeromorphicFunctionGerm.mk (polyMMer f)
          : MeromorphicFunctionGerm RiemannSphere)
        = MeromorphicFunctionGerm.mk (f - polyMMer f)
    rw [MeromorphicFunctionGerm.mk_sub]
  have h_eq_zero : (MeromorphicFunctionGerm.mk f
        - MeromorphicFunctionGerm.mk (polyMMer f)
        : MeromorphicFunctionGerm RiemannSphere) = 0 :=
    h_mk_sub.trans h_mk_diff_zero
  exact sub_eq_zero.mp h_eq_zero

/-! ## Step 7: Final discharge -/

/-- **The discharge of `LinearSystemAtInftyRS_BoundedBySimplePoleSpan`.**
Every germ in `linearSystemGermDeltaP (∞ : RS)` is in the ℂ-span of `1`
and `RSSimplePoleGerm`. -/
theorem linearSystemAtInftyRS_boundedBySimplePoleSpan :
    LinearSystemAtInftyRS_BoundedBySimplePoleSpan := by
  intro φ hφ
  -- Pick a representative.
  rcases φ with ⟨f⟩
  -- `hφ : IsBoundedByDeltaPGerm ∞ (mk f)`.
  -- By Step 6: `mk f = mk (polyMMer f) = a • 1 + b • RSSimplePoleGerm`.
  change (MeromorphicFunctionGerm.mk f : MeromorphicFunctionGerm RiemannSphere)
    ∈ Submodule.span ℂ
        ({(1 : MeromorphicFunctionGerm RiemannSphere), RSSimplePoleGerm} : Set _)
  rw [mk_f_eq_mk_polyMMer f hφ]
  -- Goal: `mk (polyMMer f) ∈ span ℂ {1, RSSimplePoleGerm}`.
  -- Show this as `a • 1 + b • RSSimplePoleGerm` directly.
  have h_mk_polyMMer_eq :
      (MeromorphicFunctionGerm.mk (polyMMer f)
        : MeromorphicFunctionGerm RiemannSphere)
      = entireRepCoeffA f • (1 : MeromorphicFunctionGerm RiemannSphere)
        + entireRepCoeffB f • RSSimplePoleGerm := by
    -- `polyMMer f = MMer.const a + b • RSSimplePoleMMer`.
    -- `mk (MMer.const a + b • RSSimplePoleMMer)
    --  = mk (a • (1 : MMer) + b • RSSimplePoleMMer)` (since `MMer.const a = a • 1` as functions)
    --  = mk (a • 1) + mk (b • RSSimplePoleMMer)
    --  = a • mk 1 + b • mk RSSimplePoleMMer
    --  = a • 1 + b • RSSimplePoleGerm`.
    -- Step 1: replace `MMer.const a` with `a • (1 : MMer)`.
    have h_const_eq : (MMer.const (entireRepCoeffA f) : MMer RiemannSphere)
        = entireRepCoeffA f • (1 : MMer RiemannSphere) := by
      apply MMer.ext
      funext x
      show entireRepCoeffA f = entireRepCoeffA f • (1 : ℂ)
      rw [smul_eq_mul, mul_one]
    show (MeromorphicFunctionGerm.mk
        (MMer.const (entireRepCoeffA f) + entireRepCoeffB f • RSSimplePoleMMer)
      : MeromorphicFunctionGerm RiemannSphere)
        = entireRepCoeffA f • (1 : MeromorphicFunctionGerm RiemannSphere)
          + entireRepCoeffB f • RSSimplePoleGerm
    rw [h_const_eq, ← MeromorphicFunctionGerm.mk_add,
      ← MeromorphicFunctionGerm.mk_smul, ← MeromorphicFunctionGerm.mk_smul]
    rfl
  rw [h_mk_polyMMer_eq]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  · refine Submodule.smul_mem _ _ ?_
    apply Submodule.subset_span
    apply Set.mem_insert_of_mem
    exact rfl

end JacobianChallenge.MeromorphicFunctionField

end
