/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackComp
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackMatrix

set_option linter.unusedSectionVars false

/-! # Composition functoriality of `pullbackMatrix` and `pushforwardLinearLift`

For composable smooth maps `f : X → Y` and `g : Y → Z` between compact
complex 1-manifolds, and chosen bases `αX, αY, αZ`:

* `pullbackMatrix αX αZ (g ∘ f) (hg.comp hf)
    = pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg`
  (matrix product, sizes `gX × gZ = gX × gY * gY × gZ`).

* `pushforwardLinearLift αX αZ (g ∘ f) (hg.comp hf)
    = (pushforwardLinearLift αY αZ g hg).comp (pushforwardLinearLift αX αY f hf)`
  (CLM composition).

These are the period-transform-side companions to `pullback_comp`
(in `HolomorphicOneFormPullbackComp.lean`). With them, the
`JacobianAnalyticPushforwardLift` bundle becomes a *covariant* functor
on the curve-map direction: `T_{g ∘ f} = T_g ∘ T_f`.
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

/-- **Composition functoriality of `pullbackMatrix`.** For composable
`f : X → Y` and `g : Y → Z`, the pullback matrix of the composition
factors as the matrix product of individual pullback matrices. -/
theorem pullbackMatrix_comp
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (αZ : Basis (Fin (JacobianChallenge.genus Z)) ℂ (HolomorphicOneForm Z))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g) :
    pullbackMatrix αX αZ (g ∘ f) (hg.comp hf)
      = pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg := by
  ext i k
  -- LHS entry (i, k) = αX.repr ((g ∘ f)^* αZ_k) i.
  -- By pullback_comp: (g ∘ f)^* αZ_k = f^* (g^* αZ_k).
  -- g^* αZ_k = ∑_j N_{j,k} αY_j  (N := pullbackMatrix αY αZ g hg).
  -- f^* (∑_j N_{j,k} αY_j) = ∑_j N_{j,k} f^* αY_j = ∑_j N_{j,k} ∑_i' M_{i',j} αX_i'
  --   (M := pullbackMatrix αX αY f hf).
  -- αX.repr at i: = ∑_j M_{i,j} N_{j,k}.
  -- RHS entry (i, k) = (M * N)_{i,k} = ∑_j M_{i,j} * N_{j,k}.
  show αX.repr (pullbackLinearMap (g ∘ f) (hg.comp hf) (αZ k)) i
    = (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k
  -- Compose: pullback (g ∘ f) ... αZ_k = pullback f ... (pullback g ... αZ_k).
  rw [pullbackLinearMap_apply, pullback_comp g hg f hf]
  -- Now: αX.repr (pullback f ... (pullback g ... (αZ k))) i = ...
  -- Expand pullback g ... αZ_k via αY basis:
  --   pullback g ... αZ_k = ∑_j N_{j,k} αY_j   (= pullbackMatrix_spec αY αZ g hg k).
  have h_g_spec : pullbackLinearMap g hg (αZ k)
      = ∑ j, pullbackMatrix αY αZ g hg j k • αY j := by
    have := @pullbackMatrix_spec Y Z _ _ _ _ _ _ αY αZ g hg k
    exact this
  -- pullback f ... is ℂ-linear, so commutes with the sum and scalar.
  show αX.repr ((pullback f hf) (pullbackLinearMap g hg (αZ k))) i = _
  rw [h_g_spec]
  -- Goal: αX.repr (pullback f hf (∑ j, M_g_{j,k} • αY_j)) i = (M_f * M_g)_{i,k}.
  -- Use the LinearMap shape to pass repr and pullback through the sum.
  have h_distribute :
      αX.repr ((pullback f hf : HolomorphicOneForm Y → HolomorphicOneForm X)
        (∑ j, pullbackMatrix αY αZ g hg j k • αY j))
      = ∑ j, pullbackMatrix αY αZ g hg j k •
          (αX.repr ((pullback f hf : _ → _) (αY j))) := by
    rw [← pullbackLinearMap_apply, map_sum, map_sum]
    simp_rw [map_smul, pullbackLinearMap_apply]
  rw [h_distribute, Finsupp.coe_finset_sum, Finset.sum_apply]
  simp_rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- Now: ∑ j, M_g_{j,k} * αX.repr (pullback f hf (αY j)) i = (M_f * M_g)_{i,k}.
  -- αX.repr (pullback f hf (αY j)) i = pullbackMatrix αX αY f hf i j by defn.
  show ∑ j, pullbackMatrix αY αZ g hg j k * pullbackMatrix αX αY f hf i j
    = (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k
  simp_rw [mul_comm (pullbackMatrix αY αZ g hg _ _) _]
  rfl

/-- **Composition functoriality of `pushforwardLinearLift`.** -/
theorem pushforwardLinearLift_comp
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (αZ : Basis (Fin (JacobianChallenge.genus Z)) ℂ (HolomorphicOneForm Z))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g) :
    pushforwardLinearLift αX αZ (g ∘ f) (hg.comp hf)
      = (pushforwardLinearLift αY αZ g hg).comp
          (pushforwardLinearLift αX αY f hf) := by
  -- pushforwardLinearLift = pullbackMatrix^T.mulVecLin.
  -- pullbackMatrix_comp: M_{gf} = M_f * M_g.
  -- (M_f * M_g)^T = M_g^T * M_f^T.
  -- (M_g^T * M_f^T).mulVec = M_g^T.mulVec ∘ M_f^T.mulVec.
  apply ContinuousLinearMap.ext
  intro v
  ext k
  rw [pushforwardLinearLift_apply, pullbackMatrix_comp αX αY αZ f hf g hg]
  -- LHS: ∑ i, (M_f * M_g)_{i,k} * v_i.
  -- RHS: pushforwardLinearLift αY αZ g hg (pushforwardLinearLift αX αY f hf v) k
  --    = ∑ j, M_g_{j,k} * (pushforwardLinearLift αX αY f hf v) j
  --    = ∑ j, M_g_{j,k} * ∑ i, M_f_{i,j} * v_i
  --    = ∑ j ∑ i, M_g_{j,k} * M_f_{i,j} * v_i.
  show ∑ i, (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k * v i
    = (((pushforwardLinearLift αY αZ g hg).comp
        (pushforwardLinearLift αX αY f hf)) v) k
  show ∑ i, (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k * v i
    = (pushforwardLinearLift αY αZ g hg
        (pushforwardLinearLift αX αY f hf v)) k
  rw [pushforwardLinearLift_apply]
  show ∑ i, (pullbackMatrix αX αY f hf * pullbackMatrix αY αZ g hg) i k * v i
    = ∑ j, pullbackMatrix αY αZ g hg j k *
        (pushforwardLinearLift αX αY f hf v) j
  simp_rw [pushforwardLinearLift_apply]
  -- After expansion:
  -- LHS = ∑ i, (∑ j, M_f_{i,j} * M_g_{j,k}) * v_i
  --     = ∑ i ∑ j, M_f_{i,j} * M_g_{j,k} * v_i.
  -- RHS = ∑ j, M_g_{j,k} * (∑ i, M_f_{i,j} * v_i)
  --     = ∑ j ∑ i, M_g_{j,k} * M_f_{i,j} * v_i.
  -- Equal after swap + commute factors.
  show ∑ i, (∑ j, pullbackMatrix αX αY f hf i j *
        pullbackMatrix αY αZ g hg j k) * v i
    = ∑ j, pullbackMatrix αY αZ g hg j k *
        ∑ i, pullbackMatrix αX αY f hf i j * v i
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext j
  congr 1
  funext i
  ring

end HolomorphicOneForm

end JacobianChallenge

end
