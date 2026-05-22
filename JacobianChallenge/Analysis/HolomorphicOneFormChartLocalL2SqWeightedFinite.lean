/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqWeighted
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2SqFinite
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Finiteness of `chartLocalL2SqWeighted` for subordinate PoU weights

Closes the finiteness atom owed by chip S.8 conditional: for a smooth
partition of unity `f` subordinate to the chart-source cover of a
compact Hausdorff complex 1-manifold, the chart-local weighted
L²-square seminorm is finite at every `y`:

```
chartLocalL2SqWeighted om y (fun x => f.toFun y x) < ⊤
```

## Argument

* `tsupport (f y) ⊆ chart-source y` (subordinacy).
* `tsupport (f y)` is closed in `X` (closure is closed) ⇒ compact
  in compact `X`.
* `chart` maps `tsupport (f y) ⊆ chart-source` injectively into the
  chart target; the image `chartAt y '' tsupport (f y)` is compact
  (continuous image of compact).
* Outside that image, the integrand `ENNReal.ofReal(χ((y).symm z)) *
  (‖lc‖₊)²` vanishes (since `(y).symm z ∉ tsupport ⇒ f y ((y).symm z)
  = 0`).
* Inside, `f y ≤ 1` (PoU values are in `Icc 0 1`), so the integrand
  is bounded by `(‖lc‖₊)²`.
* Hence the integral is dominated by `chartLocalL2Sq om y (chartAt y
  '' tsupport (f y))`, which is finite by chip B.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory ENNReal NNReal Set

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Finiteness of `chartLocalL2SqWeighted` for subordinate PoU weights.** -/
theorem chartLocalL2SqWeighted_lt_top_of_subordinate
    (om : HolomorphicOneForm X) (y : X)
    (f : SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X (Set.univ : Set X))
    (hf_subord : f.IsSubordinate (fun y : X => (chartAt ℂ y).source)) :
    chartLocalL2SqWeighted om y (fun x => f.toFun y x) < ⊤ := by
  -- Step 1: tsupport (f y) is compact in X.
  have h_tsupp_closed : IsClosed (tsupport (f.toFun y)) := isClosed_closure
  have h_tsupp_compact : IsCompact (tsupport (f.toFun y)) :=
    h_tsupp_closed.isCompact
  -- Step 2: tsupport (f y) ⊆ chart-source y (subordinacy).
  have h_tsupp_sub : tsupport (f.toFun y) ⊆ (chartAt ℂ y).source := hf_subord y
  -- Step 3: define K := chartAt y '' tsupport (f y). It's compact + ⊆ chart-target.
  set K : Set ℂ := chartAt ℂ y '' tsupport (f.toFun y) with hK_def
  have hK_compact : IsCompact K := by
    rw [hK_def]
    exact h_tsupp_compact.image_of_continuousOn
      ((chartAt ℂ y).continuousOn.mono h_tsupp_sub)
  have hK_sub : K ⊆ (chartAt ℂ y).target := by
    rw [hK_def]
    intro w hw
    obtain ⟨x, hx_in, hxw⟩ := hw
    rw [← hxw]
    exact (chartAt ℂ y).map_source (h_tsupp_sub hx_in)
  -- Step 4: integrand vanishes outside K (on chart-target \ K).
  -- For z ∈ chart-target with z ∉ K = chartAt y '' tsupport:
  --   (chartAt y).symm z ∈ source (since z ∈ target) and
  --   (chartAt y).symm z ∉ tsupport (else z ∈ K), so f y ((chartAt y).symm z) = 0.
  have h_vanish : ∀ z ∈ (chartAt ℂ y).target \ K,
      ENNReal.ofReal ((fun x => f.toFun y x) ((chartAt ℂ y).symm z))
        * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 = 0 := by
    intro z hz
    obtain ⟨hz_target, hz_notK⟩ := hz
    have h_symm_source : (chartAt ℂ y).symm z ∈ (chartAt ℂ y).source :=
      (chartAt ℂ y).map_target hz_target
    have h_symm_not_tsupp : (chartAt ℂ y).symm z ∉ tsupport (f.toFun y) := by
      intro h_in_tsupp
      apply hz_notK
      rw [hK_def]
      refine ⟨(chartAt ℂ y).symm z, h_in_tsupp, ?_⟩
      exact (chartAt ℂ y).right_inv hz_target
    have h_symm_not_supp : (chartAt ℂ y).symm z ∉ Function.support (f.toFun y) :=
      fun h => h_symm_not_tsupp (subset_closure h)
    have h_fy_zero : f.toFun y ((chartAt ℂ y).symm z) = 0 := by
      by_contra hne
      exact h_symm_not_supp hne
    show ENNReal.ofReal (f.toFun y ((chartAt ℂ y).symm z))
        * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 = 0
    rw [h_fy_zero]
    simp
  -- Step 5: bound the integrand by `(‖lc‖₊)²` on K (since f y ≤ 1, ofReal(f y) ≤ 1).
  have h_bound : ∀ z, ENNReal.ofReal ((fun x => f.toFun y x) ((chartAt ℂ y).symm z))
        * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
      ≤ (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 := by
    intro z
    have h_le_one : ENNReal.ofReal ((fun x => f.toFun y x) ((chartAt ℂ y).symm z))
        ≤ 1 := by
      have h_fxle : f.toFun y ((chartAt ℂ y).symm z) ≤ 1 := f.le_one y _
      calc ENNReal.ofReal (f.toFun y ((chartAt ℂ y).symm z))
          ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_fxle
        _ = 1 := ENNReal.ofReal_one
    calc ENNReal.ofReal ((fun x => f.toFun y x) ((chartAt ℂ y).symm z))
            * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
        ≤ 1 * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 := by
          exact mul_le_mul_right' h_le_one _
      _ = (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 := one_mul _
  -- Step 6: split chart-target into K and chart-target \ K. Integral on K bounded.
  unfold chartLocalL2SqWeighted
  -- Goal: ∫⁻ z in (chartAt ℂ y).target, ENNReal.ofReal (...) * ... < ⊤
  -- Use lintegral split: ∫⁻ over target = ∫⁻ over K + ∫⁻ over (target \ K). The
  -- second integral is 0 by h_vanish. The first is bounded by the unweighted
  -- chartLocalL2Sq on K, which is finite by chip B.
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have h_target_meas : MeasurableSet (chartAt ℂ y).target :=
    (chartAt ℂ y).open_target.measurableSet
  -- Split: target = K ∪ (target \ K).
  -- Use lintegral_mono on the integrand bound, then lintegral_inter_add_diff.
  have h_split : ∫⁻ z in (chartAt ℂ y).target,
        ENNReal.ofReal (f.toFun y ((chartAt ℂ y).symm z))
          * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 ∂(volume : Measure ℂ)
      ≤ ∫⁻ z in K,
          (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 ∂(volume : Measure ℂ) := by
    -- Pointwise: on K the bound h_bound applies; on target \ K it's 0 by h_vanish.
    -- Use that the integrand ≤ indicator K · (‖lc‖₊)².
    have h_pt : ∀ z ∈ (chartAt ℂ y).target,
        ENNReal.ofReal (f.toFun y ((chartAt ℂ y).symm z))
          * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
        ≤ Set.indicator K (fun z => (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2) z := by
      intro z hz_target
      by_cases hzK : z ∈ K
      · rw [Set.indicator_of_mem hzK]
        exact h_bound z
      · rw [Set.indicator_of_notMem hzK]
        have : ENNReal.ofReal (f.toFun y ((chartAt ℂ y).symm z))
            * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 = 0 :=
          h_vanish z ⟨hz_target, hzK⟩
        rw [this]
    have h_indicator_eq :
        ∫⁻ z in (chartAt ℂ y).target,
            Set.indicator K (fun z => (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2) z
            ∂(volume : Measure ℂ)
        = ∫⁻ z in K, (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 ∂(volume : Measure ℂ) := by
      rw [MeasureTheory.lintegral_indicator hK_meas]
      -- After indicator, ∫⁻ z in target ∩ K, ... = ∫⁻ z in K, ... (since K ⊆ target).
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact congr_arg _ (Set.inter_eq_self_of_subset_left hK_sub)
    calc ∫⁻ z in (chartAt ℂ y).target,
              ENNReal.ofReal (f.toFun y ((chartAt ℂ y).symm z))
                * (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 ∂(volume : Measure ℂ)
        ≤ ∫⁻ z in (chartAt ℂ y).target,
              Set.indicator K (fun z => (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2) z
              ∂(volume : Measure ℂ) := by
          refine MeasureTheory.setLIntegral_mono_ae' h_target_meas ?_
          exact Filter.Eventually.of_forall h_pt
      _ = ∫⁻ z in K, (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2 ∂(volume : Measure ℂ) :=
            h_indicator_eq
  -- Step 7: ∫⁻ z in K, (‖lc‖₊)² = chartLocalL2Sq om y K < ⊤ by chip B.
  have h_K_finite : chartLocalL2Sq om y K < ⊤ :=
    chartLocalL2Sq_lt_top_of_isCompact_subset_target om y hK_compact hK_sub
  -- chartLocalL2Sq om y K unfolds to the integral we have on the right of h_split.
  have h_eq_chartLocalL2Sq : ∫⁻ z in K, (‖localCoeff om y z‖₊ : ℝ≥0∞) ^ 2
      ∂(volume : Measure ℂ) = chartLocalL2Sq om y K := by
    unfold chartLocalL2Sq JacobianChallenge.L2NormSq
    rfl
  rw [h_eq_chartLocalL2Sq] at h_split
  exact lt_of_le_of_lt h_split h_K_finite

end HolomorphicOneForm

end
