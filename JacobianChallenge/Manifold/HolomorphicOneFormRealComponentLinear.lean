/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponent

/-! # `ℝ`-linearity of `realComponent` and `imagComponent` (chip PL-3d)

PL-1's `realComponent : HolomorphicOneForm X → SmoothOneForm 𝓘(ℝ, ℂ) X`
is built fibrewise from `realPartCLM`, which is a continuous **ℝ**-linear
map of the fibre `ℂ →L[ℂ] ℂ → (ℂ →L[ℝ] ℝ)`. This file lifts that
fibrewise ℝ-linearity to the section level:

* `realComponent_zero` — `realComponent (0) = 0`
* `realComponent_add` — additivity in `om`
* `realComponent_smul_real` — ℝ-scalar multiplication in `om`
* `realComponentLM : HolomorphicOneForm X →ₗ[ℝ] SmoothOneForm 𝓘(ℝ, ℂ) X` —
  bundled `LinearMap` packaging the above
* mirrored versions for `imagComponent`

Note: full **ℂ**-linearity of `realComponent` does NOT hold —
`realPartCLM` is only ℝ-linear, not ℂ-linear (since
`Re(i z) = -Im(z) ≠ i · Re(z)`). The complex case mixes
`realComponent` and `imagComponent` via the standard
`Re(a · z) = a.re Re(z) - a.im Im(z)` decomposition; see future chip.

## Why this is useful

PL-2's `complexPeriod c om := Re ∫_c om + i Im ∫_c om` decomposes
through `realComponent` and `imagComponent`. Once `complexPeriod` gains
ℝ-additivity in `om` (from PL-3d's `realComponent_add` plus the
deferred chart-pullback integrability of `SmoothPath.integrate`), the
ℂ-linearity of `complexPeriod` in `om` will follow by the
real/imaginary mixing argument. This file is the algebraic-side
prerequisite of that lift.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

universe u

/-- Local `@[ext]` lemma for `SmoothOneForm`, which is a `def` aliasing
`ContMDiffSection` and therefore does not inherit the `@[ext]` attribute
on the underlying section type. Scoped to this file. -/
@[ext] theorem SmoothOneForm.ext_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
    {ω₁ ω₂ : SmoothOneForm I X} (h : ∀ x, ω₁ x = ω₂ x) : ω₁ = ω₂ :=
  ContMDiffSection.ext h

namespace JacobianChallenge

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ### `realComponent` linearity -/

@[simp] lemma realComponent_apply (om : HolomorphicOneForm X) (x : X) :
    realComponent om x = om.realPart x := rfl

@[simp] lemma realComponent_zero :
    realComponent (0 : HolomorphicOneForm X) = 0 := by
  ext x
  -- realPart (0 : HolomorphicOneForm) x = realPartCLM ((0 : HolomorphicOneForm).eval x)
  -- = realPartCLM 0 = 0
  show realComponent (0 : HolomorphicOneForm X) x
      = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) x
  rw [realComponent_apply, ← realPartCLM_eval]
  show realPartCLM ((0 : HolomorphicOneForm X).eval x)
      = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) x
  -- (0 : HolomorphicOneForm).eval x = 0 (DFunLike coe of the zero section)
  have hzero : (0 : HolomorphicOneForm X).eval x = 0 := rfl
  rw [hzero, map_zero]
  rfl

lemma realComponent_add (om₁ om₂ : HolomorphicOneForm X) :
    realComponent (om₁ + om₂) = realComponent om₁ + realComponent om₂ := by
  ext x
  show realComponent (om₁ + om₂) x
      = (realComponent om₁ + realComponent om₂) x
  rw [realComponent_apply, ← realPartCLM_eval]
  -- (om₁ + om₂).eval x = om₁.eval x + om₂.eval x via ContMDiffSection's add
  have hadd : (om₁ + om₂).eval x = om₁.eval x + om₂.eval x := rfl
  rw [hadd, map_add]
  show realPartCLM (om₁.eval x) + realPartCLM (om₂.eval x)
      = (realComponent om₁ + realComponent om₂) x
  rw [realPartCLM_eval, realPartCLM_eval]
  rfl

lemma realComponent_smul_real (a : ℝ) (om : HolomorphicOneForm X) :
    realComponent (a • om) = a • realComponent om := by
  ext x
  show realComponent (a • om) x = (a • realComponent om) x
  rw [realComponent_apply, ← realPartCLM_eval]
  -- (a • om).eval x = a • (om.eval x), where the smul on the RHS is
  -- the ℝ-action on (ℂ →L[ℂ] ℂ) inherited via Module.compHom from the ℂ-action.
  have hsmul : (a • om).eval x = a • om.eval x := rfl
  rw [hsmul, map_smul]
  show a • realPartCLM (om.eval x) = (a • realComponent om) x
  rw [realPartCLM_eval]
  rfl

/-- `realComponent` bundled as a continuous `ℝ`-linear map of sections.
The bundle of (HolomorphicOneForm X) into (SmoothOneForm 𝓘(ℝ, ℂ) X). -/
def realComponentLM : HolomorphicOneForm X →ₗ[ℝ] SmoothOneForm 𝓘(ℝ, ℂ) X where
  toFun := realComponent
  map_add' := realComponent_add
  map_smul' := realComponent_smul_real

@[simp] lemma realComponentLM_apply (om : HolomorphicOneForm X) :
    realComponentLM om = realComponent om := rfl

/-! ### `imagComponent` linearity (mirror) -/

@[simp] lemma imagComponent_apply (om : HolomorphicOneForm X) (x : X) :
    imagComponent om x = om.imagPart x := rfl

@[simp] lemma imagComponent_zero :
    imagComponent (0 : HolomorphicOneForm X) = 0 := by
  ext x
  show imagComponent (0 : HolomorphicOneForm X) x
      = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) x
  rw [imagComponent_apply, ← imagPartCLM_eval]
  show imagPartCLM ((0 : HolomorphicOneForm X).eval x)
      = (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) x
  have hzero : (0 : HolomorphicOneForm X).eval x = 0 := rfl
  rw [hzero, map_zero]
  rfl

lemma imagComponent_add (om₁ om₂ : HolomorphicOneForm X) :
    imagComponent (om₁ + om₂) = imagComponent om₁ + imagComponent om₂ := by
  ext x
  show imagComponent (om₁ + om₂) x
      = (imagComponent om₁ + imagComponent om₂) x
  rw [imagComponent_apply, ← imagPartCLM_eval]
  have hadd : (om₁ + om₂).eval x = om₁.eval x + om₂.eval x := rfl
  rw [hadd, map_add]
  show imagPartCLM (om₁.eval x) + imagPartCLM (om₂.eval x)
      = (imagComponent om₁ + imagComponent om₂) x
  rw [imagPartCLM_eval, imagPartCLM_eval]
  rfl

lemma imagComponent_smul_real (a : ℝ) (om : HolomorphicOneForm X) :
    imagComponent (a • om) = a • imagComponent om := by
  ext x
  show imagComponent (a • om) x = (a • imagComponent om) x
  rw [imagComponent_apply, ← imagPartCLM_eval]
  have hsmul : (a • om).eval x = a • om.eval x := rfl
  rw [hsmul, map_smul]
  show a • imagPartCLM (om.eval x) = (a • imagComponent om) x
  rw [imagPartCLM_eval]
  rfl

/-- `imagComponent` bundled as a continuous `ℝ`-linear map of sections. -/
def imagComponentLM : HolomorphicOneForm X →ₗ[ℝ] SmoothOneForm 𝓘(ℝ, ℂ) X where
  toFun := imagComponent
  map_add' := imagComponent_add
  map_smul' := imagComponent_smul_real

@[simp] lemma imagComponentLM_apply (om : HolomorphicOneForm X) :
    imagComponentLM om = imagComponent om := rfl

end JacobianChallenge

end
