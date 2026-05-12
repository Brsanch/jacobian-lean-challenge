/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.MFDerivTranspose
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option diagnostics.threshold 100
set_option maxHeartbeats 400000

/-! # Function-level smoothness of the pointwise pullback

The pointwise pullback `pullbackPointwise e α : ∀ x : X, CotangentSpace x`
is, as a *function* into the fixed codomain `ℂ →L[ℂ] ℂ`, smooth at
every point. The proof factors:

* `mfderiv e x : TangentSpace x →L[ℂ] TangentSpace (e x) ≅ ℂ →L[ℂ] ℂ`
  is smooth in x by `ContMDiffAt.mfderiv_const` (mathlib).
* `α.eval (e x) : CotangentSpace (e x) ≅ ℂ →L[ℂ] ℂ` is smooth in x
  as the composition of α (smooth section) and e (smooth diffeomorph).
* Composition of CLMs is smooth (mathlib `ContMDiffAt.clm_comp`).

This file ships:

* `HolomorphicEquiv.mfderiv_inTangentCoords_contMDiffAt` — the
  tangent-coordinate smoothness of `mfderiv e`, specialised from
  `ContMDiffAt.mfderiv_const`.
* `HolomorphicEquiv.mfderiv_transpose_contMDiffAt` — the cotangent
  analogue: smoothness of the family
  `y ↦ (compL).flip (inTangentCoordinates _ _ id e (mfderiv e) x₀ y)`
  obtained by transposing `mfderiv e` to act on covectors. This is the
  `precomposition-by-mfderiv` data needed to build the pullback section.
* `HolomorphicEquiv.mfderiv_symm_inTangentCoords_contMDiffAt` and
  `HolomorphicEquiv.mfderiv_symm_transpose_contMDiffAt` — same for
  `e.symm` (the direction relevant for item-14 reverse).

Promoting these to section smoothness (required for `HolomorphicOneForm X`)
requires the cotangent-bundle in-coordinates form of
`clm_apply_of_inCoordinates`, which is the genuine bundle-pullback chip
deferred downstream.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- `1 ≤ ω` as `WithTop ℕ∞`. -/
private theorem one_le_analytic : (1 : WithTop ℕ∞) ≤ ω := by decide

/-- `2 ≤ ω` as `WithTop ℕ∞`. -/
private theorem two_le_analytic : (2 : WithTop ℕ∞) ≤ ω := by decide

/-- `ω + 1 ≤ ω` as `WithTop ℕ∞`: since `ω = ⊤`, `ω + 1 = ⊤` and the
inequality is `⊤ ≤ ⊤`. -/
private theorem analytic_succ_le_analytic : (ω + 1 : WithTop ℕ∞) ≤ ω := by
  decide

/-! ## Tangent-coordinate smoothness of `mfderiv` for a `HolomorphicEquiv` -/

/-- **Tangent-coordinate smoothness of `mfderiv e`.** For a
`HolomorphicEquiv X Y` between complex 1-manifolds modelled on `ℂ`,
the tangent-coordinate representation
`inTangentCoordinates 𝓘(ℂ) 𝓘(ℂ) id (e : X → Y) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e) x₀`
is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω` at `x₀`.

This is the manifold-derivative-smoothness lemma
`ContMDiffAt.mfderiv_const` from mathlib, specialised to the
analytic-regularity-`ω` `HolomorphicEquiv` setting. Used as the
`ϕ`-side input to `ContMDiffAt.clm_apply_of_inCoordinates` in the
pullback-section-smoothness chip. -/
theorem HolomorphicEquiv.mfderiv_inTangentCoords_contMDiffAt
    (e : HolomorphicEquiv X Y) (x₀ : X) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id (e : X → Y)
        (fun x => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x) x₀) x₀ :=
  (e.contMDiff_forward x₀).mfderiv_const analytic_succ_le_analytic

/-- **Cotangent-direction (transpose) smoothness of `mfderiv e`.** For
`e : HolomorphicEquiv X Y`, the cotangent transpose

  `y ↦ (compL ℂ ℂ ℂ ℂ).flip (inTangentCoordinates _ _ id e (mfderiv e) x₀ y)`

is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ)) ω` at `x₀`.
Direct consequence of `ContMDiffAt.mfderiv_transpose`.

This is the precomposition-by-`mfderiv-e` data ready to be plugged into
`clm_apply_of_inCoordinates` for the pullback section's smoothness. -/
theorem HolomorphicEquiv.mfderiv_transpose_contMDiffAt
    (e : HolomorphicEquiv X Y) (x₀ : X) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ))) ω
      (fun x => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id (e : X → Y)
          (fun x => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x) x₀ x)) x₀ :=
  (e.contMDiff_forward x₀).mfderiv_transpose analytic_succ_le_analytic

/-! ## Symmetric versions: `e.symm` direction (relevant for item-14 reverse) -/

/-- **Tangent-coordinate smoothness of `mfderiv e.symm`.** Symmetric
version of `HolomorphicEquiv.mfderiv_inTangentCoords_contMDiffAt`, for
the inverse biholomorphism. This is the form used in the pullback
along `e.symm : Y → X`. -/
theorem HolomorphicEquiv.mfderiv_symm_inTangentCoords_contMDiffAt
    (e : HolomorphicEquiv X Y) (y₀ : Y) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id
        (e.toEquiv.symm : Y → X)
        (fun y => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e.toEquiv.symm : Y → X) y) y₀) y₀ :=
  (e.contMDiff_inverse y₀).mfderiv_const analytic_succ_le_analytic

/-- **Cotangent transpose smoothness of `mfderiv e.symm`.** Symmetric
version of `HolomorphicEquiv.mfderiv_transpose_contMDiffAt`, for the
inverse biholomorphism. This is the `ϕ`-data appearing in the
pullback section along `e.symm : Y → X`. -/
theorem HolomorphicEquiv.mfderiv_symm_transpose_contMDiffAt
    (e : HolomorphicEquiv X Y) (y₀ : Y) :
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ))) ω
      (fun y => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id
          (e.toEquiv.symm : Y → X)
          (fun y => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            (e.toEquiv.symm : Y → X) y) y₀ y)) y₀ :=
  (e.contMDiff_inverse y₀).mfderiv_transpose analytic_succ_le_analytic

end JacobianChallenge

end
