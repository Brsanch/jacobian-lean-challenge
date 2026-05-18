/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothLoopHasMissedPointDischarge
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundFromFactorisation
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Capstone: `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀` UNCONDITIONAL

After the full pipeline:

* `smoothLoopHasMissedPointHypothesis_holds` — unconditional Sard-style
  discharge via Hausdorff dimension.
* `loopFactorsThroughVectorSpaceHypothesis_of_missedPoint` —
  case-split on missed point (∞ or finite c) using Möbius shift.
* `basedSmoothLoopsBoundHypothesis_of_factorisation` — gives
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀` from the factorisation.

The atomic predicate input is now discharged. This file ships the
unconditional composite.

## What this file ships

* `basedSmoothLoopsBoundHypothesis_RS_holds p₀` —
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RiemannSphere p₀` is true
  for any `p₀ : RiemannSphere`, unconditionally.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology

namespace JacobianChallenge

namespace RiemannSphere

/-- **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) RS p₀` holds for every
basepoint `p₀ ∈ RiemannSphere`, unconditionally.**

Composes the full pipeline:
* `smoothLoopHasMissedPointHypothesis_holds`,
* `loopFactorsThroughVectorSpaceHypothesis_of_missedPoint`,
* `basedSmoothLoopsBoundHypothesis_of_factorisation`. -/
theorem basedSmoothLoopsBoundHypothesis_RS_holds (p₀ : RiemannSphere) :
    JacobianChallenge.BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ)
      RiemannSphere p₀ := by
  apply basedSmoothLoopsBoundHypothesis_of_factorisation
  exact loopFactorsThroughVectorSpaceHypothesis_of_missedPoint p₀
    (smoothLoopHasMissedPointHypothesis_holds p₀)

end RiemannSphere

end JacobianChallenge
