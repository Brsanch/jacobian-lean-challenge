/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentFromUniformizationGenus0

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from `[UniformizationGenus0Hypothesis X]` + `genus X = 0`

End-to-end chip: under the genus-0 uniformization typeclass + a proof
genus X = 0, HJAS X follows via HJCC X.

## What ships

* `HasJacobianAnalyticStructure.of_uniformizationGenus0` — end-to-end
  constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJAS from `[UniformizationGenus0Hypothesis X]` + `genus X = 0`.** -/
theorem HasJacobianAnalyticStructure.of_uniformizationGenus0
    [UniformizationGenus0Hypothesis X]
    (h_genus : JacobianChallenge.genus X = 0) :
    HasJacobianAnalyticStructure X :=
  letI : HasJacobianClassicalContent X :=
    HasJacobianClassicalContent.of_uniformizationGenus0 h_genus
  inferInstance

end JacobianChallenge

end
