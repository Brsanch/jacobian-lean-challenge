/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentFromHolomorphicEquivRS

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from a biholomorphism `X ≃ RS`

End-to-end chip: any compact connected complex 1-manifold biholomorphic
to the Riemann sphere has `HasJacobianAnalyticStructure X`
unconditionally, via HJCC → HJAS.

## What ships

* `HasJacobianAnalyticStructure.of_holomorphicEquiv_RiemannSphere` —
  end-to-end constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` from a biholomorphism `X ≃ RS`,
end-to-end.** Composes the new HJCC-from-biholomorphism chip with the
bridge instance \`instHasJacobianAnalyticStructure_of_HasJacobianClassicalContent\`. -/
theorem HasJacobianAnalyticStructure.of_holomorphicEquiv_RiemannSphere
    (φ : HolomorphicEquiv X RiemannSphere) :
    HasJacobianAnalyticStructure X :=
  letI : HasJacobianClassicalContent X :=
    HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere φ
  inferInstance

end JacobianChallenge

end
