/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothLoopChartNPullbackDischarge

set_option linter.unusedSectionVars false

/-! # `LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀` from `SmoothLoopAvoidsInftyHypothesis`

Composite chip wiring the now-unconditional
`SmoothLoopChartNPullbackExistsHypothesis` discharge
(`SmoothLoopChartNPullbackDischarge.lean`) into the structural
reduction (`LoopFactorsThroughVectorSpaceFromChartN.lean`).

**Headline.** `SmoothLoopAvoidsInftyHypothesis p₀ → LoopFactorsThroughVectorSpaceHypothesis ℂ RiemannSphere p₀`.

After this chip, the period-lattice closure on RiemannSphere reduces
to a SINGLE atomic predicate: `SmoothLoopAvoidsInftyHypothesis p₀`,
itself constructively dischargeable via Sard + Möbius shift in a
future arc.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology

namespace JacobianChallenge

namespace RiemannSphere

variable (p₀ : RiemannSphere)

/-- **`LoopFactorsThroughVectorSpaceHypothesis ℂ RS p₀` from
`SmoothLoopAvoidsInftyHypothesis p₀` alone.**

The chart-N pullback existence side is now unconditional via
`smoothLoopChartNPullbackExistsHypothesis_holds`. -/
theorem loopFactorsThroughVectorSpaceHypothesis_of_avoidInfty
    (h_avoid : SmoothLoopAvoidsInftyHypothesis p₀) :
    JacobianChallenge.LoopFactorsThroughVectorSpaceHypothesis
      ℂ RiemannSphere p₀ :=
  loopFactorsThroughVectorSpaceHypothesis_of_avoidInfty_and_chartNPullback
    p₀ h_avoid (smoothLoopChartNPullbackExistsHypothesis_holds p₀)

end RiemannSphere

end JacobianChallenge
