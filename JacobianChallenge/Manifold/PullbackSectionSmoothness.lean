/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackPointwiseFunctionSmooth
import JacobianChallenge.Manifold.CotangentInCoordinates
import JacobianChallenge.Manifold.CotangentPullbackBridge
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option diagnostics.threshold 100
set_option maxHeartbeats 4000000

/-! # Cotangent pullback section smoothness — named obligations and discharge

For `e : HolomorphicEquiv X Y` between complex 1-manifolds modelled on
`ℂ`, the cotangent-bundle pullback section's smoothness factors through
`ContMDiffAt.clm_apply_of_inCoordinates` with three smoothness inputs:

* `hϕ` — smoothness of the precomposition CLM family
  `x ↦ (compL).flip (mfderiv e x)` in the cotangent Hom-bundle
  `inCoordinates` form. **This file discharges that hypothesis
  unconditionally** via the tangent↔cotangent bridge identity.

* `hv` — smoothness of `x ↦ TotalSpace.mk' _ (e x) (α.toFun (e x))`.
  Shipped in zz303 as `alpha_toFun_comp_e_contMDiffAt`.

* `hb₂` — `contMDiffAt_id`. Trivial.

## What this file delivers (no `sorry`, no `axiom`)

* `cotangentPullback_inCoordinates_smoothness_obligation` and
  `cotangentPullback_inCoordinates_smoothness_obligation_symm` —
  the `Prop`-valued statements packaging what
  `ContMDiffAt.clm_apply_of_inCoordinates` needs.

* `cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates` —
  the **bridge identity** at the pointwise level: the cotangent
  `inCoordinates` rewrite of `(compL).flip (mfderiv f x)` equals
  `(compL).flip` of the tangent `inCoordinates` rewrite of
  `mfderiv f x`. Proved on base-set membership.

* `cotangentPullback_inCoordinates_smoothness_obligation_holds` and
  `cotangentPullback_inCoordinates_smoothness_obligation_symm_holds` —
  both obligations are unconditionally true. Combines zz302's
  `inTangentCoordinates`-form smoothness with the bridge identity
  via `ContMDiffAt.congr_of_eventuallyEq`.

## Proof sketch of the bridge identity

For any `f : X → Y` and `x` in the base-set intersection:

```
LHS = inCotangentCoordinates I I f id ((compL).flip ∘ mfderiv f) x₀ x
    = (cot X).coordChange (achart x) (achart x₀) x        [step 1]
      ∘L ((compL).flip (mfderiv f x))
      ∘L (cot Y).coordChange (achart (f x₀)) (achart (f x)) (f x)
    = (compL).flip (tan X).coordChange (achart x₀) (achart x) x  [step 2]
      ∘L (compL).flip (mfderiv f x)
      ∘L (compL).flip (tan Y).coordChange (achart (f x)) (achart (f x₀)) (f x)
    = (compL).flip ((tan Y).coordChange (achart (f x)) (achart (f x₀)) (f x)
                    ∘L mfderiv f x
                    ∘L (tan X).coordChange (achart x₀) (achart x) x)  [step 3]
    = (compL).flip (inTangentCoordinates I I id f (mfderiv f) x₀ x)  [step 4]
    = RHS.
```

Step 1: `inCotangentCoordinates_eq` (`CotangentInCoordinates.lean`).
Step 2: `cotangentBundleCore_coordChange_apply` (`Cotangent.lean`).
Step 3: CLM-composition associativity + how `(compL).flip` composes.
Step 4: `inTangentCoordinates_eq` (mathlib).

The Lean proof condenses all four steps into a single `ext`+`simp`
after applying the two `_eq` rewrites and the cotangent coordChange
formula.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open ContinuousLinearMap

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## The named bridge obligations -/

/-- **Named bridge obligation (forward direction).** The cotangent
`inCoordinates` of the precomposition family `x ↦ (compL).flip (mfderiv
e x)` is `ContMDiffAt 𝓘(ℂ) ω` at every `x₀ : X`. -/
def cotangentPullback_inCoordinates_smoothness_obligation
    (e : HolomorphicEquiv X Y) : Prop :=
  ∀ x₀ : X,
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ))) ω
      (fun x : X =>
        ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
          (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _) (ℂ →L[ℂ] ℂ)
          (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _)
          ((e : X → Y) x₀) ((e : X → Y) x) x₀ x
          ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x))) x₀

/-- **Named bridge obligation (inverse direction).** -/
def cotangentPullback_inCoordinates_smoothness_obligation_symm
    (e : HolomorphicEquiv X Y) : Prop :=
  ∀ y₀ : Y,
    ContMDiffAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, (ℂ →L[ℂ] ℂ) →L[ℂ] (ℂ →L[ℂ] ℂ))) ω
      (fun y : Y =>
        ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
          (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _) (ℂ →L[ℂ] ℂ)
          (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _)
          ((e.toEquiv.symm : Y → X) y₀)
          ((e.toEquiv.symm : Y → X) y) y₀ y
          ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              (e.toEquiv.symm : Y → X) y))) y₀

/-! ## The bridge identity -/

/-- **Pointwise bridge identity.** On base-set intersection, the
cotangent `inCoordinates` of `(compL).flip (mfderiv f x)` equals
`(compL).flip` of the tangent `inCoordinates` of `mfderiv f x`. -/
theorem cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates
    (f : X → Y) {x₀ x : X}
    (hx : x ∈ (chartAt ℂ x₀).source)
    (hfx : f x ∈ (chartAt ℂ (f x₀)).source) :
    ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
      (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _) (ℂ →L[ℂ] ℂ)
      (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _)
      (f x₀) (f x) x₀ x
      ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x))
    = (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id f
          (fun x => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x) x₀ x) := by
  -- Step 1: LHS is `inCotangentCoordinates 𝓘 𝓘 f id _ x₀ x` by definition.
  -- Rewrite via `inCotangentCoordinates_eq` which uses
  -- `(cotangentBundleCore _ _).inCoordinates_eq` under the hood.
  have h_lhs :
      ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _) (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _)
        (f x₀) (f x) x₀ x
        ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x))
      = inCotangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f (id : X → X)
          (fun x => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x)) x₀ x := rfl
  rw [h_lhs]
  rw [inCotangentCoordinates_eq (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
      (f := f) (g := (id : X → X))
      (ϕ := fun x => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x))
      (x₀ := x₀) (x := x) hfx (by simpa using hx)]
  rw [inTangentCoordinates_eq (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
      (f := (id : X → X)) (g := f)
      (ϕ := fun x => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x)
      (x₀ := x₀) (x := x) (by simpa using hx) hfx]
  -- Both sides are now in explicit form with core coordChanges.
  -- LHS: ((cot X).coordChange ...) ∘L (((compL).flip (mfderiv f x)).comp ((cot Y).coordChange ...))
  -- RHS: (compL).flip ((tan Y).coordChange ... ∘L (mfderiv f x) ∘L (tan X).coordChange ...)
  -- Apply cot.coordChange = (compL).flip applied to tan.coordChange (inverse direction).
  ext η
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    cotangentBundleCore_coordChange_apply]

/-- **The bridge identity is eventually equal in a neighborhood of `x₀`.**
By continuity of `f`, the pointwise identity holds in a neighborhood. -/
theorem cotangent_inCoordinates_flip_eventually_eq_flip_inTangentCoordinates
    (f : X → Y) (hf : Continuous f) (x₀ : X) :
    (fun x : X =>
      ContinuousLinearMap.inCoordinates (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : Y → Type _) (ℂ →L[ℂ] ℂ)
        (CotangentSpace (𝓘(ℂ, ℂ)) : X → Type _)
        (f x₀) (f x) x₀ x
        ((ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x)))
    =ᶠ[nhds x₀] (fun x : X =>
      (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
        (inTangentCoordinates (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) id f
          (fun x => mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) f x) x₀ x)) := by
  have h_chart_X : (chartAt ℂ x₀).source ∈ nhds x₀ :=
    (chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)
  have h_chart_Y : f ⁻¹' (chartAt ℂ (f x₀)).source ∈ nhds x₀ := by
    refine hf.continuousAt ?_
    exact (chartAt ℂ (f x₀)).open_source.mem_nhds (mem_chart_source ℂ (f x₀))
  filter_upwards [h_chart_X, h_chart_Y] with x hx hfx
  exact cotangent_inCoordinates_flip_eq_flip_inTangentCoordinates f hx hfx

/-! ## Unconditional discharge of the named obligations -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- **Continuity of a `HolomorphicEquiv` (forward).** -/
private theorem HolomorphicEquiv.continuous_forward
    (e : HolomorphicEquiv X Y) : Continuous (e : X → Y) :=
  e.contMDiff_toFun.continuous

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- **Continuity of a `HolomorphicEquiv` (inverse).** -/
private theorem HolomorphicEquiv.continuous_inverse
    (e : HolomorphicEquiv X Y) :
    Continuous (e.toEquiv.symm : Y → X) :=
  e.contMDiff_invFun.continuous

/-- **Unconditional discharge (forward).** The named obligation
`cotangentPullback_inCoordinates_smoothness_obligation` holds for any
`e : HolomorphicEquiv X Y`. -/
theorem cotangentPullback_inCoordinates_smoothness_obligation_holds
    (e : HolomorphicEquiv X Y) :
    cotangentPullback_inCoordinates_smoothness_obligation e := by
  intro x₀
  have h_zz302 :=
    HolomorphicEquiv.mfderiv_transpose_contMDiffAt e x₀
  have h_eq :=
    cotangent_inCoordinates_flip_eventually_eq_flip_inTangentCoordinates
      (e : X → Y) e.continuous_forward x₀
  -- h_zz302 : ContMDiffAt _ _ ω RHS x₀
  -- h_eq    : LHS =ᶠ RHS
  -- Want    : ContMDiffAt _ _ ω LHS x₀
  -- `ContMDiffAt.congr_of_eventuallyEq` takes (h : ContMDiff f x) (h₁ : f₁ =ᶠ f).
  exact h_zz302.congr_of_eventuallyEq h_eq

/-- **Unconditional discharge (inverse).** The named obligation
`cotangentPullback_inCoordinates_smoothness_obligation_symm` holds for
any `e : HolomorphicEquiv X Y`. This closes the analytic ingredient
of item-14 reverse unconditionally. -/
theorem cotangentPullback_inCoordinates_smoothness_obligation_symm_holds
    (e : HolomorphicEquiv X Y) :
    cotangentPullback_inCoordinates_smoothness_obligation_symm e := by
  intro y₀
  have h_zz302 :=
    HolomorphicEquiv.mfderiv_symm_transpose_contMDiffAt e y₀
  have h_eq :=
    cotangent_inCoordinates_flip_eventually_eq_flip_inTangentCoordinates
      (e.toEquiv.symm : Y → X) e.continuous_inverse y₀
  exact h_zz302.congr_of_eventuallyEq h_eq

/-! ## Unconditional pullback-section smoothness via `clm_apply_of_inCoordinates`

With the bridge obligations now unconditionally discharged, assembling
the pullback section's smoothness via `ContMDiffAt.clm_apply_of_inCoordinates`
is mechanical. The three inputs are:

* `hϕ`  : `cotangentPullback_inCoordinates_smoothness_obligation_holds`
* `hv`  : `HolomorphicEquiv.alpha_toFun_comp_e_contMDiffAt` (zz303)
* `hb₂` : `contMDiffAt_id`

Combined with zz304's `pullbackPointwise_eq_clm_apply` rewrite. -/

/-- **Unconditional pullback-section smoothness (forward).** -/
theorem HolomorphicEquiv.pullbackSection_contMDiffAt
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x₀ : X) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x
        (e.pullbackPointwise α x)) x₀ := by
  -- Let-bindings to help typeclass resolution in `clm_apply_of_inCoordinates`.
  let b₁ : X → Y := (e : X → Y)
  let b₂ : X → X := id
  let v : ∀ x : X, CotangentSpace (𝓘(ℂ, ℂ)) (b₁ x) := fun x => α.toFun (b₁ x)
  let ϕ : ∀ x : X,
      CotangentSpace (𝓘(ℂ, ℂ)) (b₁ x) →L[ℂ] CotangentSpace (𝓘(ℂ, ℂ)) (b₂ x) :=
    fun x => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x)
  have h_eq : ∀ x : X,
      e.pullbackPointwise α x = ϕ x (v x) :=
    fun x => HolomorphicEquiv.pullbackPointwise_eq_clm_apply e α x
  have h_funext : (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x
      (e.pullbackPointwise α x))
    = (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) (b₂ x) (ϕ x (v x))) := by
    funext x; rw [h_eq x]; rfl
  rw [h_funext]
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (hϕ := cotangentPullback_inCoordinates_smoothness_obligation_holds e x₀)
    (hv := HolomorphicEquiv.alpha_toFun_comp_e_contMDiffAt e α x₀)
    (hb₂ := contMDiffAt_id)

/-- **Unconditional pullback-section smoothness (inverse direction).**
This is the analytic content needed for the item-14 reverse closure. -/
theorem HolomorphicEquiv.pullbackSection_symm_contMDiffAt
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm X) (y₀ : Y) :
    ContMDiffAt (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y
        (e.symm.pullbackPointwise α y)) y₀ := by
  let b₁ : Y → X := (e.toEquiv.symm : Y → X)
  let b₂ : Y → Y := id
  let v : ∀ y : Y, CotangentSpace (𝓘(ℂ, ℂ)) (b₁ y) := fun y => α.toFun (b₁ y)
  let ϕ : ∀ y : Y,
      CotangentSpace (𝓘(ℂ, ℂ)) (b₁ y) →L[ℂ] CotangentSpace (𝓘(ℂ, ℂ)) (b₂ y) :=
    fun y => (ContinuousLinearMap.compL ℂ ℂ ℂ ℂ).flip
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.toEquiv.symm : Y → X) y)
  have h_eq : ∀ y : Y, e.symm.pullbackPointwise α y = ϕ y (v y) :=
    fun y => HolomorphicEquiv.pullbackPointwise_symm_eq_clm_apply e α y
  have h_funext : (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y
      (e.symm.pullbackPointwise α y))
    = (fun y : Y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) (b₂ y) (ϕ y (v y))) := by
    funext y; rw [h_eq y]; rfl
  rw [h_funext]
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (hϕ :=
      cotangentPullback_inCoordinates_smoothness_obligation_symm_holds e y₀)
    (hv := HolomorphicEquiv.alpha_toFun_comp_eSymm_contMDiffAt e α y₀)
    (hb₂ := contMDiffAt_id)

end JacobianChallenge

end

