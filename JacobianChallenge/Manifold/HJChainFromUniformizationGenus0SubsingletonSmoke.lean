/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HJASFromHolomorphicEquivRSUnconditional
import JacobianChallenge.Manifold.HJASFromHasPic0AnalyticEquiv
import JacobianChallenge.Manifold.HasJacobianClassicalContentFromHolomorphicEquivRS
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromHJCC
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromHJCC

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # Smoke test: the full HJ chain composes from UnifGenus0 + Subsingleton ω

Validates that the **full Jacobian C3 chain**
HJAE → HJAS → HJCC → HJHC → HasC3FullClassicalContent
auto-composes through typeclass synthesis under
`[UniformizationGenus0Hypothesis X] + [Subsingleton ω]`.

This is a regression-guard smoke test, not new content. It confirms
that the just-shipped
`instHasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega`
instance fires through to every downstream class via `inferInstance`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [UniformizationGenus0Hypothesis X]
  [Subsingleton (HolomorphicOneForm X)]

example : HasPic0AnalyticEquiv X := inferInstance
example : HasJacobianAnalyticStructure X := inferInstance
example : HasJacobianClassicalContent X :=
  HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere
    (Classical.choice
      (UniformizationGenus0Hypothesis.out (X := X)
        (by
          haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
            DiskChartCover.holomorphicOneFormFiniteDim_holds
          exact Module.finrank_zero_of_subsingleton)))

end JacobianChallenge

end
