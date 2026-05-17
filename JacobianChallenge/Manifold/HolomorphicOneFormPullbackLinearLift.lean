/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrix
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrixId
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrixComp
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrixConst

set_option linter.unusedSectionVars false

/-! # `pullbackLinearLift` — the sister CLM to `pushforwardLinearLift`

For a smooth curve map `f : X → Y` between compact complex 1-manifolds
with chosen bases `αX, αY`, define the **pullback linear lift**:

  `pullbackLinearLift αX αY f hf : (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ)`

as `pullbackMatrix αX αY f hf` interpreted as a CLM via `mulVecLin`
(no transpose, unlike the pushforward case). This is the
analytic-Jacobian-side CLM that lifts the form-level pullback
`f^* : HolomorphicOneForm Y → HolomorphicOneForm X` to the period-vector
covers.

Functoriality witnesses for `(id, comp, const)` parallel those for
`pushforwardLinearLift`:

* `pullbackLinearLift_id` — equals `ContinuousLinearMap.id`.
* `pullbackLinearLift_comp` — `T_{g ∘ f} = T_f ∘ T_g` (contravariant
  composition).
* `pullbackLinearLift_const` — equals `0` at a constant curve map.
-/

open scoped Manifold ContDiff
open Submodule Module

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]

/-- The **pullback linear lift**: the CLM `(Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ)`
obtained from `pullbackMatrix αX αY f hf` via `Matrix.mulVecLin` (no
transpose).

Sister to `pushforwardLinearLift` (which uses `M^T.mulVecLin` to obtain
`(Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ)`). -/
noncomputable def pullbackLinearLift
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
      (Fin (JacobianChallenge.genus X) → ℂ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin (pullbackMatrix αX αY f hf))

/-- Definitional unfolding of `pullbackLinearLift`. -/
theorem pullbackLinearLift_apply
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (w : Fin (JacobianChallenge.genus Y) → ℂ) (i) :
    pullbackLinearLift αX αY f hf w i
      = ∑ j, pullbackMatrix αX αY f hf i j * w j := by
  show (Matrix.mulVecLin (pullbackMatrix αX αY f hf) w) i = _
  rfl

/-- **Identity functoriality of `pullbackLinearLift`.** -/
theorem pullbackLinearLift_id
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)) :
    pullbackLinearLift αX αX (id : X → X) contMDiff_id
      = ContinuousLinearMap.id ℂ (Fin (JacobianChallenge.genus X) → ℂ) := by
  apply ContinuousLinearMap.ext
  intro w
  ext i
  rw [pullbackLinearLift_apply, pullbackMatrix_id]
  show ∑ j, (1 : Matrix _ _ ℂ) i j * w j = w i
  simp [Matrix.one_apply, Finset.sum_ite_eq]

/-- **Constant-map case of `pullbackLinearLift`.** Equals `0`. -/
theorem pullbackLinearLift_const
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (y₀ : Y) :
    pullbackLinearLift αX αY (fun _ : X => y₀) contMDiff_const
      = (0 : (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
              (Fin (JacobianChallenge.genus X) → ℂ)) := by
  apply ContinuousLinearMap.ext
  intro w
  ext i
  rw [pullbackLinearLift_apply, pullbackMatrix_const]
  show ∑ j, (0 : Matrix _ _ ℂ) i j * w j =
    (0 : (Fin (JacobianChallenge.genus Y) → ℂ) →L[ℂ]
            (Fin (JacobianChallenge.genus X) → ℂ)) w i
  simp [Matrix.zero_apply]

/-- **Composition functoriality of `pullbackLinearLift`** (contravariant). -/
theorem pullbackLinearLift_comp
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (αZ : Basis (Fin (JacobianChallenge.genus Z)) ℂ (HolomorphicOneForm Z))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g) :
    pullbackLinearLift αX αZ (g ∘ f) (hg.comp hf)
      = (pullbackLinearLift αX αY f hf).comp
          (pullbackLinearLift αY αZ g hg) := by
  apply ContinuousLinearMap.ext
  intro w
  ext i
  rw [pullbackLinearLift_apply, pullbackMatrix_comp αX αY αZ f hf g hg]
  -- LHS: ∑ k, (M_f * M_g)_{i,k} * w_k
  --    = ∑ k, (∑ j, M_f_{i,j} M_g_{j,k}) * w_k
  --    = ∑ k ∑ j, M_f_{i,j} M_g_{j,k} w_k.
  -- RHS: ((pullbackLinearLift f).comp (pullbackLinearLift g)) w i
  --    = pullbackLinearLift f (pullbackLinearLift g w) i
  --    = ∑ j, M_f_{i,j} * (pullbackLinearLift g w) j
  --    = ∑ j, M_f_{i,j} * ∑ k, M_g_{j,k} * w_k
  --    = ∑ j ∑ k, M_f_{i,j} M_g_{j,k} w_k.
  -- Equal after swap.
  show ∑ k, (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k * w k
    = (((pullbackLinearLift αX αY f hf).comp
        (pullbackLinearLift αY αZ g hg)) w) i
  show ∑ k, (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k * w k
    = pullbackLinearLift αX αY f hf
        (pullbackLinearLift αY αZ g hg w) i
  rw [pullbackLinearLift_apply]
  simp_rw [pullbackLinearLift_apply]
  -- After expansion:
  -- LHS = ∑ k, (∑ j, M_f_{i,j} * M_g_{j,k}) * w_k
  -- RHS = ∑ j, M_f_{i,j} * (∑ k, M_g_{j,k} * w_k)
  show ∑ k, (∑ j, pullbackMatrix αX αY f hf i j *
        pullbackMatrix αY αZ g hg j k) * w k
    = ∑ j, pullbackMatrix αX αY f hf i j *
        ∑ k, pullbackMatrix αY αZ g hg j k * w k
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext k
  congr 1
  funext j
  ring

end HolomorphicOneForm

end JacobianChallenge

end
