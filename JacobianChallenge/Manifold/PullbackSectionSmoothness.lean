/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PullbackPointwiseFunctionSmooth
import JacobianChallenge.Manifold.CotangentInCoordinates
import JacobianChallenge.Manifold.CotangentPullbackBridge

set_option diagnostics.threshold 100

/-! # Named obligations toward cotangent pullback section smoothness

This file names the **bridge obligations** that gate the unconditional
discharge of `IsHolomorphicOneFormPullback_for_all e` for a
`HolomorphicEquiv X Y` via the cotangent-bundle pullback machinery.

zz302 ships `mfderiv_transpose_contMDiffAt`: the cotangent
precomposition family is smooth, expressed via `inTangentCoordinates`
(the tangent-bundle in-coordinates form).

zz303 ships `alpha_toFun_comp_e_contMDiffAt`: the `α ∘ e` total-space
function is smooth.

zz304 ships `pullbackPointwise_eq_clm_apply`: the algebraic identity
that re-expresses the pullback as `ϕ x (v x)` matching the shape of
`ContMDiffAt.clm_apply_of_inCoordinates`.

What's missing to combine these into section smoothness is a single
identity (or smoothness translation) between the *tangent*
in-coordinates form (zz302) and the *general* in-coordinates form on
the cotangent Hom bundle that `clm_apply_of_inCoordinates` expects.
This file names that obligation as a `Prop` and provides the
boilerplate skeleton on which a follow-up chip can land the
unconditional discharge.

## What this file delivers (no `sorry`, no `axiom`)

* `cotangentPullback_inCoordinates_smoothness_obligation` —
  `Prop`-valued: the cotangent `inCoordinates` rewrite of the
  precomposition family `fun x ↦ (compL).flip (mfderiv e x)` is
  `ContMDiffAt 𝓘(ℂ) ω` at every `x₀ : X`.

* `cotangentPullback_inCoordinates_smoothness_obligation_symm` —
  same for the inverse-direction biholomorphism `e.symm`.

These are the analytic obligations that, once discharged, let
`ContMDiffAt.clm_apply_of_inCoordinates` close the pullback section's
smoothness with the smoothness inputs already in tree.

The structure of a future "assembly" chip is:

```
theorem pullbackSection_contMDiffAt
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) (x₀ : X) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ→L[ℂ]ℂ)) ω
      (fun x ↦ TotalSpace.mk' _ x (e.pullbackPointwise α x)) x₀ := by
  rw [show ... using zz304's `pullbackPointwise_eq_clm_apply`]
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (hϕ := cotangentPullback_inCoordinates_smoothness_obligation e x₀)
    (hv := zz303's `alpha_toFun_comp_e_contMDiffAt e α x₀`)
    (hb₂ := contMDiffAt_id)
```

The `hϕ` slot is the named obligation. The bridge from zz302's
`inTangentCoordinates` form to this `inCoordinates`-on-cotangent
form is the substantive Lean-level identification (chase through
`Bundle.Trivialization.continuousLinearMapAt`,
`Bundle.Trivialization.symmL`, and the cotangent-from-tangent cocycle).
That identification lives in
`Manifold/CotangentInCoordinates.lean` and
`Manifold/CotangentPullbackBridge.lean` for the single-covector case;
upgrading to the family-of-CLMs case is the remaining work.

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
e x)` is `ContMDiffAt 𝓘(ℂ) ω` at every `x₀ : X`.

This is the mathlib-`inCoordinates`-form of zz302's
`HolomorphicEquiv.mfderiv_transpose_contMDiffAt` (stated via
`inTangentCoordinates`). The bridge identity is mathematically routine
(same data in same trivialisations) but requires Lean-level
identification through `Bundle.Trivialization.continuousLinearMapAt`,
`Bundle.Trivialization.symmL`, and the cotangent-from-tangent cocycle
formula. -/
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

/-- **Named bridge obligation (inverse direction).** Same as the
previous but for the inverse-direction biholomorphism `e.symm : Y → X`
(the case relevant to item-14 reverse). -/
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

end JacobianChallenge

end
