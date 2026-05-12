/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional discharge of every hypothesis in the
identity-theorem reduction chain

The chain
```
ClopennessOfLocallyConstHypothesis      ← terminal residual
  ↓ chartOverlapPropagation_of_clopennessOfLocallyConst
ChartOverlapPropagationHypothesis
  ↓ chartPullbackNotEventuallyConst_of_chartOverlapPropagation
ChartPullbackNotEventuallyConstHypothesis
  ↓ chartBallOffCentreWitness_of_chartPullbackNotEventuallyConst
ChartBallOffCentreWitnessHypothesis
  ↓ perChartNonConstancy_of_chartBallOffCentreWitness
PerChartNonConstancyHypothesis
  ↓ withinChartWitness_of_perChartNonConstancy
WithinChartWitnessHypothesis
  ↓ connectivityGlobalization_of_withinChartWitness
ConnectivityGlobalizationHypothesis
```
was reduced step-by-step in the `*Discharge.lean` /
`*Reduction.lean` files, and the terminal residual
`ClopennessOfLocallyConstHypothesis` was itself discharged
unconditionally in `ClopennessOfLocallyConstDischarge.lean`
(`clopennessOfLocallyConst_holds`).

This file packages the composition: each named hypothesis in the chain
gets a corresponding `*_holds_unconditional` lemma with no hypotheses
beyond the manifold typeclasses on `X` and `Y`. These are direct
compositions of existing chain reducers with the terminal
unconditional discharge — no new mathematical content, no new named
hypotheses, no `sorry`, no `axiom`. The point is API tidiness:
downstream consumers that want, say, `PerChartNonConstancyHypothesis`
no longer need to manually thread `clopennessOfLocallyConst_holds`
through `perChartNonConstancy_of_clopennessOfLocallyConst` — they can
reference `perChartNonConstancyHypothesis_holds_unconditional`
directly.

All six lemmas have identical typeclass shape, identical proof shape
(one application of a chain reducer to the terminal
`clopennessOfLocallyConst_holds`), and are stated in the same namespace
as the underlying hypotheses (`JacobianChallenge.ContMDiff.Owed.degree`).
-/

@[expose] public section

open scoped Manifold ContDiff

namespace JacobianChallenge
namespace ContMDiff
namespace Owed.degree

universe u v

/-- **Unconditional discharge of `ChartOverlapPropagationHypothesis`.**
Composition of the terminal unconditional
`clopennessOfLocallyConst_holds` with the chain reducer
`chartOverlapPropagation_of_clopennessOfLocallyConst`. -/
theorem chartOverlapPropagationHypothesis_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ChartOverlapPropagationHypothesis X Y :=
  chartOverlapPropagation_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

/-- **Unconditional discharge of
`ChartPullbackNotEventuallyConstHypothesis`.** Composition of the
terminal unconditional `clopennessOfLocallyConst_holds` with the chain
reducer `chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst`. -/
theorem chartPullbackNotEventuallyConstHypothesis_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ChartPullbackNotEventuallyConstHypothesis X Y :=
  chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

/-- **Unconditional discharge of
`ChartBallOffCentreWitnessHypothesis`.** -/
theorem chartBallOffCentreWitnessHypothesis_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ChartBallOffCentreWitnessHypothesis X Y :=
  chartBallOffCentreWitness_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

/-- **Unconditional discharge of
`PerChartNonConstancyHypothesis`.** The most-consumed intermediate
hypothesis: downstream files like
`RamificationIndexCompUnconditional.lean`,
`FibreDisjointChartRadiusDecomposition.lean`, and
`RamificationIndexPositive.lean` currently obtain this by composing
`clopennessOfLocallyConst_holds` with
`perChartNonConstancy_of_clopennessOfLocallyConst` inline. This wrapper
shortens the boilerplate to a single name. -/
theorem perChartNonConstancyHypothesis_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    PerChartNonConstancyHypothesis X Y :=
  perChartNonConstancy_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

/-- **Unconditional discharge of
`WithinChartWitnessHypothesis`.** -/
theorem withinChartWitnessHypothesis_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    WithinChartWitnessHypothesis X Y :=
  withinChartWitness_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

/-- **Unconditional discharge of
`ConnectivityGlobalizationHypothesis`.** -/
theorem connectivityGlobalizationHypothesis_holds_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ConnectivityGlobalizationHypothesis X Y :=
  connectivityGlobalization_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

end Owed.degree
end ContMDiff
end JacobianChallenge
