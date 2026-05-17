/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SheetCotangentPullbackContMDiffAt
import JacobianChallenge.Manifold.HolomorphicCotangentPullbackAt

/-! # `HolomorphicOneForm.pullback` for general smooth maps

For any smooth map `g : Y → X` between complex 1-manifolds (i.e.,
`ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g`), the **pullback of holomorphic
1-forms**

  `g^* : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y`
  `g^* α (y) := (α.toFun (g y)).comp (mfderiv g y)`

is a well-defined ℂ-linear map.

The pointwise content `holCotangentPullbackAt g y α` is in
`HolomorphicCotangentPullbackAt.lean`. The **smoothness of the section**
`y ↦ holCotangentPullbackAt g y α` is in
`SheetCotangentPullbackContMDiffAt.lean` (`pullbackSection_contMDiffAt_of_localSheet`).

This file packages those two ingredients into a single ℂ-linear map.

## Why this is needed

OPEN.md items 18 and 21 (`pushforward_contMDiff`, `pullback_contMDiff`)
require, on the analytic Jacobian level, a ℂ-linear cover lift
`T_g : ℂ^{gX} →L[ℂ] ℂ^{gY}` (or reverse direction for pushforward)
induced by `g`. The natural construction is via the **basis matrix
of the pullback map** `g^* : HolOneForm X → HolOneForm Y` against
chosen bases `αX` and `αY`. The `T_g` carries period vectors in `X`
to period vectors in `Y` via the formula

  `T_g (period(γ)) = period(g_* γ)` for `γ ∈ H₁(X; ℤ)`.

(Or the transpose, depending on direction.)

This file delivers the linear map. The basis-matrix construction
(`T_g`) and the period-lattice-matching certificate live in
follow-up chips.

## Net contribution

* `HolomorphicOneForm.pullback (g : Y → X) (hg : ContMDiff ω g) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y` — the ℂ-linear
  pullback map.

* `HolomorphicOneForm.pullback_apply` — definitional unfold.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace HolomorphicOneForm

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-- **Pullback of holomorphic 1-forms along a smooth map.**

For `g : Y → X` with `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g`, and a
holomorphic 1-form `α : HolomorphicOneForm X`, the pullback
`g^* α : HolomorphicOneForm Y` has underlying section
`y ↦ (α.toFun (g y)).comp (mfderiv g y)`. -/
noncomputable def pullback
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (α : HolomorphicOneForm X) :
    HolomorphicOneForm Y :=
  ⟨fun y => holCotangentPullbackAt g y α,
   fun y =>
     pullbackSection_contMDiffAt_of_localSheet g (hg y) α⟩

/-- Definitional unfolding of `pullback`: the underlying section
agrees pointwise with `holCotangentPullbackAt`. -/
theorem pullback_apply
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (α : HolomorphicOneForm X) (y : Y) :
    (pullback g hg α).toFun y = holCotangentPullbackAt g y α := rfl

/-- The pullback of `0` is `0`. -/
@[simp] theorem pullback_zero
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g) :
    pullback g hg (0 : HolomorphicOneForm X) = (0 : HolomorphicOneForm Y) := by
  apply ContMDiffSection.ext
  intro y
  show (pullback g hg 0).toFun y = (0 : HolomorphicOneForm Y).toFun y
  rw [pullback_apply, holCotangentPullbackAt_zero]
  rfl

/-- The pullback is additive. -/
@[simp] theorem pullback_add
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (α₁ α₂ : HolomorphicOneForm X) :
    pullback g hg (α₁ + α₂) = pullback g hg α₁ + pullback g hg α₂ := by
  apply ContMDiffSection.ext
  intro y
  show (pullback g hg (α₁ + α₂)).toFun y =
    (pullback g hg α₁ + pullback g hg α₂).toFun y
  rw [pullback_apply, holCotangentPullbackAt_add]
  show holCotangentPullbackAt g y α₁ + holCotangentPullbackAt g y α₂ =
    (pullback g hg α₁).toFun y + (pullback g hg α₂).toFun y
  rw [pullback_apply, pullback_apply]

/-- The pullback is ℂ-linear. -/
@[simp] theorem pullback_smul
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (c : ℂ) (α : HolomorphicOneForm X) :
    pullback g hg (c • α) = c • pullback g hg α := by
  apply ContMDiffSection.ext
  intro y
  show (pullback g hg (c • α)).toFun y = (c • pullback g hg α).toFun y
  rw [pullback_apply, holCotangentPullbackAt_smul]
  show c • holCotangentPullbackAt g y α = c • (pullback g hg α).toFun y
  rw [pullback_apply]

/-- **Pullback as a ℂ-linear map.** Packages `pullback` plus the
`pullback_add` and `pullback_smul` lemmas as a `LinearMap`. -/
noncomputable def pullbackLinearMap
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g) :
    HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y where
  toFun := pullback g hg
  map_add' := pullback_add g hg
  map_smul' := pullback_smul g hg

/-- Definitional unfolding of `pullbackLinearMap`. -/
@[simp] theorem pullbackLinearMap_apply
    (g : Y → X) (hg : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g)
    (α : HolomorphicOneForm X) :
    pullbackLinearMap g hg α = pullback g hg α := rfl

end HolomorphicOneForm

end JacobianChallenge

end
