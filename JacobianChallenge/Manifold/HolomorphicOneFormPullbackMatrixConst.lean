/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackConst
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrix

set_option linter.unusedSectionVars false

/-! # `pullbackMatrix` / `pushforwardLinearLift` at a constant map = 0

For a constant curve map `fun _ => y₀ : X → Y`, the basis matrix of the
pullback is the zero matrix, and the pushforward linear lift is the
zero CLM.

Functoriality witnesses for the constant-curve-map case (mirror of
`pullbackMatrix_id`, `pushforwardLinearLift_id`).
-/

open scoped Manifold ContDiff
open Submodule Module

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- The pullback matrix at a constant map is the zero matrix. -/
theorem pullbackMatrix_const
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (y₀ : Y) :
    pullbackMatrix αX αY (fun _ : X => y₀) contMDiff_const
      = (0 : Matrix (Fin (JacobianChallenge.genus X))
            (Fin (JacobianChallenge.genus Y)) ℂ) := by
  ext i j
  show αX.repr ((pullbackLinearMap (fun _ : X => y₀) contMDiff_const) (αY j)) i
    = (0 : Matrix _ _ ℂ) i j
  rw [pullbackLinearMap_const]
  show αX.repr ((0 : HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X)
      (αY j)) i = _
  rw [LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
  rfl

/-- The pushforward linear lift at a constant map is the zero CLM. -/
theorem pushforwardLinearLift_const
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (y₀ : Y) :
    pushforwardLinearLift αX αY (fun _ : X => y₀) contMDiff_const
      = (0 : (Fin (JacobianChallenge.genus X) → ℂ) →L[ℂ]
              (Fin (JacobianChallenge.genus Y) → ℂ)) := by
  apply ContinuousLinearMap.ext
  intro v
  ext j
  rw [pushforwardLinearLift_apply, pullbackMatrix_const]
  show ∑ i, (0 : Matrix _ _ ℂ) i j * v i =
    (0 : (Fin (JacobianChallenge.genus X) → ℂ) →L[ℂ]
            (Fin (JacobianChallenge.genus Y) → ℂ)) v j
  simp [Matrix.zero_apply]

end HolomorphicOneForm

end JacobianChallenge

end
