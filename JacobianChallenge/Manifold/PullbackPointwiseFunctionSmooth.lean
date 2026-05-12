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

/-! ## `v`-side smoothness: `α ∘ e` as a total-space-valued map

For `α : HolomorphicOneForm Y` and `e : HolomorphicEquiv X Y`, the
function `x ↦ TotalSpace.mk' (ℂ →L[ℂ] ℂ) (e x) (α.toFun (e x))` valued
in the total space of the cotangent bundle of `Y` is `ContMDiff` on `X`.

This is the `v`-side input of `ContMDiffAt.clm_apply_of_inCoordinates`
in the pullback-section-smoothness chip: `α` as a smooth section,
composed with `e` (smooth), is smooth as a total-space-valued function.

The shape `TotalSpace.mk' F b f` matches the form used in
`RiemannSphereChartNHolomorphy.lean` (which compiles), avoiding the
`T%`-elaborator's typeclass-search issues through the
`HolomorphicOneForm = def` boundary. -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **`v`-side smoothness.** Composition of a holomorphic 1-form on `Y`
with a `HolomorphicEquiv X Y`, viewed as a total-space-valued function. -/
theorem HolomorphicEquiv.alpha_toFun_comp_e_contMDiff
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) :
    ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) (e x)
        (α.toFun ((e : X → Y) x))) :=
  α.contMDiff.comp e.contMDiff_forward

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **`v`-side smoothness, pointwise.** -/
theorem HolomorphicEquiv.alpha_toFun_comp_e_contMDiffAt
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x₀ : X) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) (e x)
        (α.toFun ((e : X → Y) x))) x₀ :=
  (HolomorphicEquiv.alpha_toFun_comp_e_contMDiff e α).contMDiffAt

omit [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- **`v`-side for `e.symm`.** For the inverse biholomorphism, the
composition `α ∘ e.symm` (as a total-space-valued function on `Y`) is
`ContMDiff`. This is the `v`-side input for the pullback section in
the `Y → X` (item-14 reverse) direction. -/
theorem HolomorphicEquiv.alpha_toFun_comp_eSymm_contMDiff
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) :
    ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        ((e.toEquiv.symm : Y → X) y)
        (α.toFun ((e.toEquiv.symm : Y → X) y))) :=
  α.contMDiff.comp e.contMDiff_inverse

omit [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- **`v`-side for `e.symm`, pointwise.** -/
theorem HolomorphicEquiv.alpha_toFun_comp_eSymm_contMDiffAt
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) (y₀ : Y) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        ((e.toEquiv.symm : Y → X) y)
        (α.toFun ((e.toEquiv.symm : Y → X) y))) y₀ :=
  (HolomorphicEquiv.alpha_toFun_comp_eSymm_contMDiff e α).contMDiffAt

/-! ## Pullback as a `clm_apply` shape

The pointwise pullback `(α.eval (e x)).comp (mfderiv e x)` can be
re-expressed as `ϕ x (v x)` where `ϕ x = (compL).flip (mfderiv e x)`
(the `ϕ`-side) and `v x = α.toFun (e x)` (the `v`-side). This matches
the shape required by `ContMDiffAt.clm_apply_of_inCoordinates` exactly,
so the eventual section-smoothness chip can rewrite the pullback via
this identity, then invoke the mathlib lemma with the smoothness inputs
shipped in zz302 and zz303. -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- **`pullbackPointwise` as `clm_apply`.** The pointwise pullback
factors as `((compL).flip (mfderiv e x)) (α.toFun (e x))` — i.e., as
the application of the precomposition CLM (`ϕ`-side, smoothness from
zz302) to the form-value (`v`-side, smoothness from zz303). -/
theorem HolomorphicEquiv.pullbackPointwise_eq_clm_apply
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x : X) :
    e.pullbackPointwise α x
      = ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x))
            (α.toFun ((e : X → Y) x)) := by
  -- LHS = (α.eval (e x)).comp (mfderiv e x), by definition.
  -- RHS unfolds via `compL.flip` to the same composition.
  show ContinuousLinearMap.comp (HolomorphicOneForm.eval α ((e : X → Y) x))
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x)
    = ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x))
          (α.toFun ((e : X → Y) x))
  ext
  -- HolomorphicOneForm.eval α (e x) = α.toFun (e x) (defeq via DFunLike on
  -- ContMDiffSection unfold).
  have h_eval : HolomorphicOneForm.eval α ((e : X → Y) x)
      = α.toFun ((e : X → Y) x) := rfl
  rw [h_eval]
  rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- **`pullbackPointwise` along `e.symm` as `clm_apply`.** Symmetric
version for the inverse-direction pullback, used in item-14 reverse. -/
theorem HolomorphicEquiv.pullbackPointwise_symm_eq_clm_apply
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) (y : Y) :
    e.symm.pullbackPointwise α y
      = ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            (e.toEquiv.symm : Y → X) y))
            (α.toFun ((e.toEquiv.symm : Y → X) y)) := by
  show ContinuousLinearMap.comp (HolomorphicOneForm.eval α
      ((e.symm : Y → X) y))
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.symm : Y → X) y)
    = _
  ext
  have h_eval : HolomorphicOneForm.eval α ((e.symm : Y → X) y)
      = α.toFun ((e.toEquiv.symm : Y → X) y) := rfl
  rw [h_eval]
  rfl

end JacobianChallenge

end

