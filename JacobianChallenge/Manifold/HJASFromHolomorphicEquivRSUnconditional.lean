/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquivHolomorphicEquivRSUnconditional
import JacobianChallenge.Manifold.HJASFromHasPic0AnalyticEquiv

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from a biholomorphism `X ≃ω RS`, UNCONDITIONAL

Chains:
* `hasPic0AnalyticEquiv_of_holomorphicEquiv_RS` (this session) — HJAE X
  from a biholomorphism X ≃ω RS, unconditional.
* `instHasJacobianAnalyticStructure_of_HasPic0AnalyticEquiv` (in tree) —
  HJAS X auto-derives from HJAE X.

Composing gives HJAS X from a biholomorphism, fully unconditional.

## What ships

* `hasJacobianAnalyticStructure_of_holomorphicEquiv_RS` — HJAS X from
  HolomorphicEquiv X RiemannSphere, unconditional.
* `hasJacobianAnalyticStructure_of_uniformizationGenus0_subsingleton_omega` —
  HJAS X from `[UniformizationGenus0Hypothesis X] + [Subsingleton ω]`,
  unconditional.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJAS X from a biholomorphism `X ≃ω RS`, unconditional.** -/
theorem hasJacobianAnalyticStructure_of_holomorphicEquiv_RS
    (φ : HolomorphicEquiv X RiemannSphere) :
    HasJacobianAnalyticStructure X := by
  haveI : HasPic0AnalyticEquiv X := hasPic0AnalyticEquiv_of_holomorphicEquiv_RS φ
  exact inferInstance

/-- **HJAS X from `UniformizationGenus0Hypothesis X + Subsingleton ω`,
unconditional.** -/
theorem hasJacobianAnalyticStructure_of_uniformizationGenus0_subsingleton_omega
    [UniformizationGenus0Hypothesis X]
    [Subsingleton (HolomorphicOneForm X)] :
    HasJacobianAnalyticStructure X := by
  haveI : HasPic0AnalyticEquiv X :=
    hasPic0AnalyticEquiv_of_uniformizationGenus0_subsingleton_omega
  exact inferInstance

end JacobianChallenge

end
