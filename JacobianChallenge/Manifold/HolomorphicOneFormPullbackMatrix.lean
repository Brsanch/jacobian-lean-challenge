/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackGeneral
import JacobianChallenge.Manifold.HolomorphicOneForm
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Basis-matrix form of the holomorphic-1-form pullback

Given a smooth `f : X → Y` between compact connected complex
1-manifolds, and chosen bases

  * `αX : Basis (Fin gX) ℂ (HolomorphicOneForm X)`,
  * `αY : Basis (Fin gY) ℂ (HolomorphicOneForm Y)`,

the **pullback matrix** of `f^* : HolomorphicOneForm Y → HolomorphicOneForm X`
in these bases is `M : Matrix (Fin gX) (Fin gY) ℂ` with entries

  `M i j = (αX.repr (f^* αY_j)) i`

i.e., `f^* αY_j = ∑_i M_{i,j} αX_i`.

Period vectors transform contravariantly: for a cycle `γ` on `X`,
the pushed-forward cycle `f_* γ` on `Y` has period vector against
`αY` equal to `M^T · (period(γ))` (matrix-transpose applied to the
period vector of `γ` against `αX`).

This file builds:

* `pullbackMatrix αX αY f hf : Matrix (Fin gX) (Fin gY) ℂ` — the
  matrix above;
* `pushforwardLinearLift αX αY f hf : (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ)`
  — the ContinuousLinearMap defined by `M.transpose.mulVecLin`, i.e.,
  the period-pushforward transform. This is the lift `T_f` for
  `JacobianAnalyticPushforwardLift` modulo the period-lattice-matching
  certificate (to be supplied via the period-pairing machinery in
  follow-up chips).

## Net contribution

* Builds the basis-matrix and the continuous linear-map shape of `T_f`
  for OPEN.md items 18 + 21, from the general
  `HolomorphicOneForm.pullbackLinearMap`.

* Defers `lattice_match` to a follow-up: the certificate is the
  classical statement "period vectors of cycles in `X` map under
  the basis-matrix transpose to period vectors of cycles in `Y`",
  which is the standard adjunction `∫_{f_*γ} αY_j = ∫_γ f^* αY_j`.
-/

open scoped Manifold ContDiff
open Submodule Module

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Pullback matrix in chosen bases.** Entry `(i, j)` is the
coefficient of `αX i` in `f^* (αY j)`. -/
noncomputable def pullbackMatrix
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    Matrix (Fin (JacobianChallenge.genus X))
           (Fin (JacobianChallenge.genus Y)) ℂ :=
  Matrix.of (fun i j => αX.repr (pullbackLinearMap f hf (αY j)) i)

/-- Defining identity: `f^* αY_j = ∑_i M_{i,j} αX_i`. -/
theorem pullbackMatrix_spec
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (j : Fin (JacobianChallenge.genus Y)) :
    pullbackLinearMap f hf (αY j) =
      ∑ i, pullbackMatrix αX αY f hf i j • αX i := by
  -- `f^* αY_j = αX.repr.symm (αX.repr (f^* αY_j))`
  --          = ∑_i (αX.repr (f^* αY_j))_i • αX_i.
  conv_lhs => rw [← αX.linearCombination_repr (pullbackLinearMap f hf (αY j))]
  simp [Finsupp.linearCombination, Finsupp.sum_fintype, pullbackMatrix,
    Matrix.of_apply]

/-- **Pushforward linear lift `T_f`** for the analytic-Jacobian-level
pushforward.

Built from `pullbackMatrix^T` so that `T_f` is the period-transform of
the cycle-pushforward direction: for a cycle `γ ⊆ X` with period
vector `(∫_γ αX_i)_i ∈ ℂ^{gX}`, `T_f` sends it to the period vector of
`f_* γ ⊆ Y` against `αY`, which equals `M^T · period(γ) ∈ ℂ^{gY}` by
the adjunction `∫_{f_*γ} αY_j = ∫_γ f^* αY_j`.

The lattice-matching certificate (carrying the X-period image into the
Y-period image) is the classical content of the same adjunction, to be
discharged via period-pairing infrastructure in a follow-up chip. -/
noncomputable def pushforwardLinearLift
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) :
    (Fin (JacobianChallenge.genus X) → ℂ) →L[ℂ]
      (Fin (JacobianChallenge.genus Y) → ℂ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.mulVecLin (pullbackMatrix αX αY f hf).transpose)

/-- Definitional unfolding of `pushforwardLinearLift`. -/
theorem pushforwardLinearLift_apply
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (v : Fin (JacobianChallenge.genus X) → ℂ) (j) :
    pushforwardLinearLift αX αY f hf v j
      = ∑ i, pullbackMatrix αX αY f hf i j * v i := by
  -- `M^T.mulVec v j = ∑_i M^T_{j i} * v_i = ∑_i M_{i j} * v_i`.
  show (Matrix.mulVecLin (pullbackMatrix αX αY f hf).transpose v) j
    = _
  rfl

end HolomorphicOneForm

end JacobianChallenge

end
