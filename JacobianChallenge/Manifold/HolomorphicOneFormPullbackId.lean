/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackGeneral

set_option linter.unusedSectionVars false

/-! # Functoriality of `pullback` at identity

For the identity map `id : X → X`:

* `pullback id contMDiff_id α = α` for every `α : HolomorphicOneForm X`.
* `pullbackLinearMap id contMDiff_id = LinearMap.id`.

Reason: `holCotangentPullbackAt id x α = (α x).comp (mfderiv id x)
       = (α x).comp ContinuousLinearMap.id
       = α x`.

This is the cleanest functoriality witness for the analytic-Jacobian-
level pushforward lift: under `id`, the lift `T_id` is the identity
matrix, hence the identity continuous linear map, hence trivially
matches lattices.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- `mfderiv` of `id : X → X` at every point is `ContinuousLinearMap.id`. -/
private lemma mfderiv_id_eq (x : X) :
    mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (id : X → X) x =
      ContinuousLinearMap.id ℂ (TangentSpace (𝓘(ℂ, ℂ)) x) :=
  mfderiv_id

/-- The pointwise pullback along the identity is the identity. -/
theorem holCotangentPullbackAt_id (x : X) (α : HolomorphicOneForm X) :
    holCotangentPullbackAt (id : X → X) x α = α.toFun x := by
  show (α.toFun ((id : X → X) x)).comp
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (id : X → X) x) = α.toFun x
  rw [mfderiv_id_eq]
  exact ContinuousLinearMap.comp_id _

/-- The pullback along the identity is the identity (pointwise / extensional). -/
theorem pullback_id (α : HolomorphicOneForm X) :
    pullback (id : X → X) contMDiff_id α = α := by
  apply ContMDiffSection.ext
  intro x
  show (pullback (id : X → X) contMDiff_id α).toFun x = α.toFun x
  rw [pullback_apply, holCotangentPullbackAt_id]

/-- `pullbackLinearMap` along the identity equals `LinearMap.id`. -/
theorem pullbackLinearMap_id :
    pullbackLinearMap (id : X → X) contMDiff_id
      = (LinearMap.id : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm X) := by
  ext α
  simp [pullbackLinearMap_apply, pullback_id]

end HolomorphicOneForm

end JacobianChallenge

end
