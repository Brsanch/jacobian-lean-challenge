/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusGlobalLiftExtended
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Bump multiplier on T²: smooth ℝ → ℝ bump with `= 1` on `Icc 0 1`

For a positive radius `δ : ℝ`, build a smooth bump function
`smoothBump δ : ℝ → ℝ` that equals `1` on `Icc 0 1` and `0` outside
`Icc (-δ/2) (1 + δ/2)`. Uses `Real.smoothTransition` (smooth 0→1
transition).

`smoothBump δ t :=
   Real.smoothTransition (2 * t / δ + 1) *
   Real.smoothTransition ((2 + δ - 2 * t) / δ)`

* For `t ≤ -δ/2`: first factor `= smoothTransition(≤ 0) = 0`. `bump = 0`.
* For `-δ/2 < t < 0`: first transitions `0 → 1`, second `= 1`.
* For `0 ≤ t ≤ 1`: both factors `= 1`. `bump = 1`.
* For `1 < t < 1 + δ/2`: first `= 1`, second transitions `1 → 0`.
* For `t ≥ 1 + δ/2`: second factor `= 0`. `bump = 0`.

## What this file ships

* `ComplexTorus.smoothBump` — the smooth bump function.

* `ComplexTorus.smoothBump_contDiff` — `smoothBump δ` is `ContDiff ℝ ∞`.

* `ComplexTorus.smoothBump_eq_one_on_Icc01` — `smoothBump δ t = 1` for
  `t ∈ Icc 0 1`.

* `ComplexTorus.smoothBump_eq_zero_left` — `smoothBump δ t = 0` for
  `t ≤ -δ/2`.

* `ComplexTorus.smoothBump_eq_zero_right` — `smoothBump δ t = 0` for
  `t ≥ 1 + δ/2`.

No `sorry`, no `axiom`. -/

open Set Metric
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

/-! ## The smooth bump function -/

/-- **Smooth bump function**: `smoothBump δ` is `1` on `Icc 0 1` and
`0` outside `Icc (-δ/2) (1 + δ/2)`. -/
noncomputable def smoothBump (δ : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition (2 * t / δ + 1) *
    Real.smoothTransition ((2 + δ - 2 * t) / δ)

/-! ## Smoothness -/

theorem smoothBump_contDiff (δ : ℝ) :
    ContDiff ℝ ∞ (smoothBump δ) := by
  unfold smoothBump
  refine ContDiff.mul ?_ ?_
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-! ## Equal to `1` on `Icc 0 1` -/

theorem smoothBump_eq_one_on_Icc01 {δ : ℝ} (hδ_pos : 0 < δ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    smoothBump δ t = 1 := by
  unfold smoothBump
  -- First factor: 2t/δ + 1. At t ≥ 0, this is ≥ 1. smoothTransition ≥ 1 = 1.
  have h1 : (1 : ℝ) ≤ 2 * t / δ + 1 := by
    have h_nn : 0 ≤ 2 * t / δ := by
      apply div_nonneg _ hδ_pos.le
      linarith [ht.1]
    linarith
  -- Second factor: (2 + δ - 2t)/δ. At t ≤ 1, this is (2 + δ - 2t)/δ ≥ (2 + δ - 2)/δ = 1.
  have h2 : (1 : ℝ) ≤ (2 + δ - 2 * t) / δ := by
    rw [le_div_iff₀ hδ_pos]
    linarith [ht.2]
  rw [Real.smoothTransition.one_of_one_le h1,
      Real.smoothTransition.one_of_one_le h2]
  ring

/-! ## Equal to `0` outside support -/

theorem smoothBump_eq_zero_left {δ : ℝ} (hδ_pos : 0 < δ) {t : ℝ}
    (ht : t ≤ -δ / 2) :
    smoothBump δ t = 0 := by
  unfold smoothBump
  -- First factor: 2t/δ + 1 ≤ 0. From t ≤ -δ/2 → 2t ≤ -δ → 2t/δ ≤ -1.
  have h_2t_le : 2 * t ≤ -δ := by linarith
  have h_div_le : 2 * t / δ ≤ -1 := by
    rw [div_le_iff₀ hδ_pos]
    linarith
  have h1 : 2 * t / δ + 1 ≤ 0 := by linarith
  rw [Real.smoothTransition.zero_of_nonpos h1]
  ring

theorem smoothBump_eq_zero_right {δ : ℝ} (hδ_pos : 0 < δ) {t : ℝ}
    (ht : 1 + δ / 2 ≤ t) :
    smoothBump δ t = 0 := by
  unfold smoothBump
  -- Second factor: (2 + δ - 2t)/δ ≤ 0. Numerator ≤ 0, denominator ≥ 0.
  have h_num : 2 + δ - 2 * t ≤ 0 := by linarith
  have h2 : (2 + δ - 2 * t) / δ ≤ 0 := by
    rw [div_nonpos_iff]
    right
    exact ⟨h_num, hδ_pos.le⟩
  rw [Real.smoothTransition.zero_of_nonpos h2]
  ring

/-! ## ContMDiff form for use in manifold context -/

theorem smoothBump_contMDiff (δ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (smoothBump δ) :=
  (contMDiff_iff_contDiff (f := smoothBump δ) (n := ∞)).mpr (smoothBump_contDiff δ)

end ComplexTorus

end JacobianChallenge

end
