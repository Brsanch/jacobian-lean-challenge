/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Analysis.HolomorphicOneFormChartLocalL2Sq
import JacobianChallenge.Manifold.HolomorphicOneFormChartCoeffOnTarget
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Chart-local L²-square seminorm is finite on compact subsets of the chart target

For `om : HolomorphicOneForm X`, `y : X`, and a compact set
`K ⊆ (chartAt ℂ y).target`, the chart-local L²-square seminorm
`chartLocalL2Sq om y K : ℝ≥0∞` is **finite** (`< ⊤`).

Proof: `HolomorphicOneForm.localCoeff_analyticOn`
(`Manifold/HolomorphicOneFormChartCoeffOnTarget.lean:309`) gives
`AnalyticOn ℂ (localCoeff om y) (chartAt ℂ y).target`, hence
continuity on `K`. A continuous function from a compact set to a
normed group is bounded
(`IsCompact.exists_bound_of_continuousOn`); call the bound `C`. Then

```
∫⁻ z in K, ‖localCoeff om y z‖₊^2 ∂volume
  ≤ ∫⁻ z in K, C.toNNReal^2 ∂volume
  = C.toNNReal^2 * volume K
```

is the product of a finite ENNReal with the finite Lebesgue volume
of a compact subset of ℂ, hence `< ⊤`.

Headline:

```
theorem chartLocalL2Sq_lt_top_of_isCompact_subset_target
    (om : HolomorphicOneForm X) (y : X)
    {K : Set ℂ} (hK_compact : IsCompact K)
    (hK_sub : K ⊆ (chartAt ℂ y).target) :
    chartLocalL2Sq om y K < ⊤
```

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory ENNReal NNReal

namespace HolomorphicOneForm

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **`localCoeff om y` is `ContinuousOn` the chart target.** Immediate
from `localCoeff_analyticOn`. -/
lemma localCoeff_continuousOn (om : HolomorphicOneForm X) (y : X) :
    ContinuousOn (localCoeff om y) (chartAt ℂ y).target :=
  (localCoeff_analyticOn om y).continuousOn

/-- **Chart-local L²-square seminorm is finite on a compact subset of
the chart target.**

The substantive content of chip B in the L²-positivity arc for
`RiemannSecondRelationPositivity` at general genus: each chart-local
slice of the Petersson L²-norm is a finite real number, so the
partition-of-unity sum (chip C, downstream) will be a well-typed
real number rather than an `⊤`-valued sum. -/
theorem chartLocalL2Sq_lt_top_of_isCompact_subset_target
    (om : HolomorphicOneForm X) (y : X)
    {K : Set ℂ} (hK_compact : IsCompact K)
    (hK_sub : K ⊆ (chartAt ℂ y).target) :
    chartLocalL2Sq om y K < ⊤ := by
  -- Continuity on K via restriction from chart target.
  have h_cont : ContinuousOn (localCoeff om y) K :=
    (localCoeff_continuousOn om y).mono hK_sub
  -- Compact-set bound on ‖localCoeff om y‖.
  obtain ⟨C, hC⟩ :=
    hK_compact.exists_bound_of_continuousOn h_cont
  -- ‖f z‖₊^2 ≤ C.toNNReal^2 for z ∈ K.
  have h_bound :
      ∀ z ∈ K, (‖localCoeff om y z‖₊ : ℝ≥0∞)^2
        ≤ ((C.toNNReal : ℝ≥0∞))^2 := by
    intro z hz
    have hz_le : ‖localCoeff om y z‖ ≤ C := hC z hz
    -- ‖f z‖.toNNReal = ‖f z‖₊ since ‖·‖ ≥ 0.
    have h_eq : Real.toNNReal ‖localCoeff om y z‖ = ‖localCoeff om y z‖₊ := by
      ext; rw [Real.coe_toNNReal _ (norm_nonneg _), coe_nnnorm]
    -- ‖f z‖.toNNReal ≤ C.toNNReal via Real.toNNReal_mono.
    have h_nn : ‖localCoeff om y z‖₊ ≤ C.toNNReal := by
      rw [← h_eq]; exact Real.toNNReal_mono hz_le
    -- Cast to ENNReal.
    have hf_nn : (‖localCoeff om y z‖₊ : ℝ≥0∞) ≤ ((C.toNNReal : ℝ≥0∞)) := by
      exact_mod_cast h_nn
    exact pow_le_pow_left' hf_nn 2
  -- Bound the lintegral on K by the constant integral.
  have h_lint_le :
      ∫⁻ z in K, (‖localCoeff om y z‖₊ : ℝ≥0∞)^2 ∂(volume : Measure ℂ)
        ≤ ∫⁻ _ in K, ((C.toNNReal : ℝ≥0∞))^2 ∂(volume : Measure ℂ) := by
    refine setLIntegral_mono_ae' hK_compact.measurableSet ?_
    exact Filter.Eventually.of_forall h_bound
  -- The constant integral equals C.toNNReal^2 * volume(K).
  have h_const :
      ∫⁻ _ in K, ((C.toNNReal : ℝ≥0∞))^2 ∂(volume : Measure ℂ)
        = ((C.toNNReal : ℝ≥0∞))^2 * (volume : Measure ℂ) K := by
    rw [setLIntegral_const]
  -- volume(K) < ⊤ since K is compact in ℂ.
  have h_vol_lt : (volume : Measure ℂ) K < ⊤ := hK_compact.measure_lt_top
  -- C.toNNReal^2 < ⊤ since it's a coercion of a finite NNReal.
  have h_C_lt : ((C.toNNReal : ℝ≥0∞))^2 < ⊤ :=
    ENNReal.pow_lt_top ENNReal.coe_lt_top
  -- Combine.
  unfold chartLocalL2Sq JacobianChallenge.L2NormSq
  calc
    ∫⁻ x, (‖localCoeff om y x‖₊ : ℝ≥0∞)^2 ∂((volume : Measure ℂ).restrict K)
      ≤ ∫⁻ _ in K, ((C.toNNReal : ℝ≥0∞))^2 ∂(volume : Measure ℂ) := h_lint_le
    _ = ((C.toNNReal : ℝ≥0∞))^2 * (volume : Measure ℂ) K := h_const
    _ < ⊤ := ENNReal.mul_lt_top h_C_lt h_vol_lt

end HolomorphicOneForm

end
