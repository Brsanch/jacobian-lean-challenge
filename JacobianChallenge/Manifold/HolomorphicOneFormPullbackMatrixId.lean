/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackId
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrix

set_option linter.unusedSectionVars false

/-! # `pullbackMatrix` and `pushforwardLinearLift` at the identity

Specialisations of `pullbackMatrix` and `pushforwardLinearLift`
(in `HolomorphicOneFormPullbackMatrix.lean`) to the identity map
`id : X → X` against the same basis `αX` on both sides.

* `pullbackMatrix αX αX id contMDiff_id = 1` (identity matrix).
* `pushforwardLinearLift αX αX id contMDiff_id = ContinuousLinearMap.id`.

These functoriality witnesses underwrite the eventual
`JacobianAnalyticPushforwardLift.id` constructor: for `f := id`, the
lift `T_id` is the identity `ℂ^{gX} →L[ℂ] ℂ^{gX}`, automatically
matching `data_X.lattice` with itself.
-/

open scoped Manifold ContDiff
open Submodule Module

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- The pullback matrix at the identity is the identity matrix. -/
theorem pullbackMatrix_id
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    pullbackMatrix αX αX (id : X → X) contMDiff_id
      = (1 : Matrix (Fin (JacobianChallenge.genus X))
            (Fin (JacobianChallenge.genus X)) ℂ) := by
  ext i j
  -- LHS = αX.repr (pullbackLinearMap id contMDiff_id (αX j)) i
  --     = αX.repr (αX j) i  (by pullbackLinearMap_id)
  --     = if i = j then 1 else 0  (basis duality)
  -- RHS = 1 i j = if i = j then 1 else 0.
  show αX.repr ((pullbackLinearMap (id : X → X) contMDiff_id) (αX j)) i
    = (1 : Matrix _ _ ℂ) i j
  rw [pullbackLinearMap_id]
  -- Now: αX.repr (αX j) i = (1 : Matrix _ _ ℂ) i j.
  show αX.repr (αX j) i = (1 : Matrix _ _ ℂ) i j
  simp [αX.repr_self, Finsupp.single_apply, Matrix.one_apply, eq_comm]

/-- The pushforward linear lift at the identity is the identity CLM. -/
theorem pushforwardLinearLift_id
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    pushforwardLinearLift αX αX (id : X → X) contMDiff_id
      = ContinuousLinearMap.id ℂ (Fin (JacobianChallenge.genus X) → ℂ) := by
  -- pushforwardLinearLift = (M^T).mulVecLin.toCLM
  -- At id, M = 1, M^T = 1, so mulVecLin = LinearMap.id, and .toCLM = CLM.id.
  apply ContinuousLinearMap.ext
  intro v
  -- Reduce to coordinates.
  ext j
  rw [pushforwardLinearLift_apply, pullbackMatrix_id]
  -- Goal: ∑ i, (1 : Matrix _ _ ℂ) i j * v i = (ContinuousLinearMap.id ℂ _) v j
  show ∑ i, (1 : Matrix _ _ ℂ) i j * v i = v j
  simp [Matrix.one_apply, Finset.sum_ite_eq']

end HolomorphicOneForm

end JacobianChallenge

end
