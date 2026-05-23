/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquivSubsingletonDirect
import JacobianChallenge.Manifold.SubsingletonHolomorphicOneFormFromBiholomorphism
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundTransport
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere
import JacobianChallenge.Manifold.Pic0RiemannSphereSubsingleton

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasPic0AnalyticEquiv X` from a biholomorphism `X ≃ RS`

Final composition: any compact connected complex 1-manifold X
biholomorphic to `RiemannSphere` has `HasPic0AnalyticEquiv X`,
**provided** we have `Subsingleton (Pic0 X)`. The latter doesn't
transport unconditionally along biholomorphism in tree (would require
Pic0-functorial transport), so we leave it as a hypothesis.

In practice, on any X biholomorphic to RS the Pic0 subsingleton holds
classically (Pic⁰ X ≃ Pic⁰ RS = 0); the in-tree chip
`subsingleton_pic0_RiemannSphere` provides RS's case, and a
biholomorphism-driven transport would give X's case.

## What ships

* `hasPic0AnalyticEquiv_of_holomorphicEquiv_RS_subsingleton_pic0` —
  HJAE X from a biholomorphism + Subsingleton (Pic0 X).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJAE X from biholomorphism X ≃ RS + Subsingleton (Pic0 X).** -/
theorem hasPic0AnalyticEquiv_of_holomorphicEquiv_RS_subsingleton_pic0
    [Subsingleton (Pic0 X)]
    (φ : HolomorphicEquiv X RiemannSphere) :
    HasPic0AnalyticEquiv X := by
  -- Subsingleton ω via the existing chip.
  haveI : Subsingleton (HolomorphicOneForm X) :=
    subsingleton_holomorphicOneForm_of_holomorphicEquiv_RS φ
  -- BSLB on X at φ.symm q₀ for some q₀.
  let q₀ : RiemannSphere := Classical.arbitrary _
  have h_bslb :
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X
        ((φ.symm : HolomorphicEquiv RiemannSphere X).toEquiv q₀) :=
    basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism
      (φ.symm : HolomorphicEquiv RiemannSphere X) q₀
      (JacobianChallenge.RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds q₀)
  exact hasPic0AnalyticEquiv_of_subsingleton_omega_subsingleton_pic0_BSLB _ h_bslb

end JacobianChallenge

end
