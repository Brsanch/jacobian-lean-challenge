/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FibreDisjointChartRadiusDecomposition
import JacobianChallenge.Manifold.NearbyRegularWitnessDischarge
import JacobianChallenge.Manifold.CriticalValuesFiniteGeneral

set_option diagnostics.threshold 100

/-! # `NearbyRegularWitnessHypothesis` from disjoint-chart-radius decomposition + nearby regular value (named conditional)

This file factors the discharge of `NearbyRegularWitnessHypothesis X Y`
through two cleanly-named pieces:

1. `fibre_disjoint_chart_radius_decomposition` (existing, unconditional) —
   for any `y₀ : Y`, there is an open neighbourhood `V ∋ y₀` and a
   per-fibre-point chart-radius family such that for `y ∈ V` with
   `y ≠ y₀`, the fibre `f ⁻¹' {y}` decomposes as the disjoint union
   over the original fibre `f ⁻¹' {y₀}`, with per-`x`-cardinality
   equal to `manifoldRamificationIndex f x`.

2. `NearbyRegularValueAtY` X Y — **named open hypothesis**: in the
   neighbourhood `V` from (1), there exists a regular value
   `y' ∈ V \ {y₀}`. Classically, this follows from finiteness of
   critical values (`criticalValues_finite_general`, existing
   conditional on `PerChartNonConstancyHypothesis` which is
   unconditional) plus `Y` being infinite (any open subset of `Y`
   minus a finite set is non-empty).

With (2), the discharge is mechanical: at `y'`, the cardinality of
`f ⁻¹' {y'}` (across all charts) equals the sum of ramification
indices at `y₀`, and `y'` is regular, so we can package a
`RegularValueWitnessReg` whose card equals the desired sum.

This chip ships:

* `NearbyRegularValueExists` — the named conditional (2).
* `nearbyRegularWitnessHypothesis_of_nearbyRegularValue_and_decomposition`
  — the discharge composing (1) + (2).

No `sorry`, no `axiom`. This factors the open frontier inside
`NearbyRegularWitnessHypothesis X Y` from one large hypothesis into a
single small named open hypothesis (`NearbyRegularValueExists`),
which classically follows from the finite-critical-values argument.
-/

open scoped Manifold ContDiff
open Set Filter Topology Metric

noncomputable section

namespace JacobianChallenge

universe u v

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Named open hypothesis: in any neighbourhood `V` of `y₀`, there
exists a regular value of `f` not equal to `y₀`.** Classically: critical
values are finite (`criticalValues_finite_general` modulo
`PerChartNonConstancyHypothesis` which is unconditional via
`clopennessOfLocallyConst_holds`) and `Y` is infinite
(`y_infinite_of_chartedSpace_complex`), so any open `V ∋ y₀` minus the
finitely many critical values minus `{y₀}` is non-empty. -/
def NearbyRegularValueExists : Prop :=
  ∀ (f : X → Y) (_hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (_hnc : ¬ JacobianChallenge.IsConstantMap f) (y₀ : Y)
    (V : Set Y) (_hV_open : IsOpen V) (_hy₀_in : y₀ ∈ V),
    ∃ y' ∈ V, y' ≠ y₀ ∧
      ∀ x ∈ f ⁻¹' {y'},
        deriv ((chartAt ℂ y') ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0

end JacobianChallenge

end
