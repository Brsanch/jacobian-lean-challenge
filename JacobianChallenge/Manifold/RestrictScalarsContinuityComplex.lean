/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasFDerivAtRestrictScalarsComplex
import Mathlib.Analysis.Normed.Operator.Basic

set_option linter.unusedSectionVars false

/-! # Hand-rolled continuity of `ContinuousLinearMap.restrictScalars ℝ` for `ℂ → ℂ` maps

Mathlib's `ContinuousLinearMap.continuous_restrictScalars` requires an
`IsScalarTower ℝ ℂ ℂ` typeclass instance that hits the same diamond as
the higher-level `ContDiffOn.restrict_scalars`. This file ships a
**hand-rolled** continuity proof that bypasses the diamond by using
only the explicit operator-norm bound
`‖(f.restrictScalars ℝ) x‖ = ‖f x‖ ≤ ‖f‖ * ‖x‖` (which gives
`‖f.restrictScalars ℝ‖ ≤ ‖f‖` for the ℝ-operator norm, via
`opNorm_le_bound`).

This unblocks `ContDiffOn ℝ 1`-level bridging for `ℂ → ℂ` functions
in `HolomorphicOneFormChartCoeffOnTarget`-imported contexts.

## What this file ships

* `continuous_restrictScalars_complex` — `Continuous (· .restrictScalars ℝ)`
  for `ℂ →L[ℂ] ℂ → ℂ →L[ℝ] ℂ`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Topology

/-- **Hand-rolled continuity** of `(·.restrictScalars ℝ) : (ℂ →L[ℂ] ℂ) → (ℂ →L[ℝ] ℂ)`.

Bypasses the `IsScalarTower ℝ ℂ ℂ` diamond hit by mathlib's
`ContinuousLinearMap.continuous_restrictScalars`. Proof: the map is
additive (`(g₁ - g₂).restrictScalars ℝ = g₁.restrictScalars ℝ -
g₂.restrictScalars ℝ` by `rfl`); 1-Lipschitz on differences via
`‖(g₁ - g₂).restrictScalars ℝ‖ ≤ ‖g₁ - g₂‖` (immediate from
`opNorm_le_bound` + `(g₁ - g₂).le_opNorm`). -/
theorem continuous_restrictScalars_complex :
    Continuous (fun g : ℂ →L[ℂ] ℂ => g.restrictScalars ℝ) := by
  rw [Metric.continuous_iff]
  intro g ε hε
  refine ⟨ε, hε, ?_⟩
  intro g' hg'
  rw [dist_eq_norm] at *
  have h_add : g'.restrictScalars ℝ - g.restrictScalars ℝ
             = (g' - g).restrictScalars ℝ := rfl
  rw [h_add]
  refine lt_of_le_of_lt ?_ hg'
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    (fun x => (g' - g).le_opNorm x)

end
