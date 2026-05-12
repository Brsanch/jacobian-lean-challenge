/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Smoothness obligation for the holomorphic-1-form pullback

zz289 ships the pointwise function-level pullback
`HolomorphicEquiv.pullbackPointwise e α : ∀ x : X, CotangentSpace 𝓘(ℂ) x`.
To upgrade this function into a genuine `HolomorphicOneForm X` we
need the smoothness (analyticity) of the section.

This file:

1. Names the per-form pullback-as-section as a `Prop` via the
   existence of a `HolomorphicOneForm X` whose underlying function
   equals the pointwise pullback.
2. Provides the trivial unconditional discharge for the case when the
   codomain's 1-form space is subsingleton — every form is zero, the
   pullback is the zero function, and the zero section *is* an
   `HolomorphicOneForm X` (namely the zero form).
3. Specialises this to `Y = RiemannSphere`, where zz274 gives the
   subsingleton instance unconditionally.

The construction of a real smooth pullback for arbitrary `Y` requires
the cotangent-bundle transition machinery in
`Manifold/CotangentPullbackBridge.lean` and is deferred to a downstream
chip.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## Pullback-as-section: existence of a `HolomorphicOneForm X` matching the pointwise pullback -/

/-- **Pullback-as-section existence.** There exists a holomorphic
1-form on `X` whose underlying section equals the pointwise pullback
`e.pullbackPointwise α`. -/
def IsHolomorphicOneFormPullback
    (e : HolomorphicEquiv X Y) (α : HolomorphicOneForm Y) : Prop :=
  ∃ pα : HolomorphicOneForm X,
    ∀ x : X, HolomorphicOneForm.eval pα x
      = e.pullbackPointwise α x

/-- **Universal form.** Every pointwise pullback along `e` is realised
by a `HolomorphicOneForm X`. -/
def IsHolomorphicOneFormPullback_for_all
    (e : HolomorphicEquiv X Y) : Prop :=
  ∀ α : HolomorphicOneForm Y, IsHolomorphicOneFormPullback e α

/-! ## Trivial discharge in the subsingleton case

When `HolomorphicOneForm Y` is subsingleton, every form is `0`, so the
pointwise pullback is the zero function, and the zero
`HolomorphicOneForm X` realises it. -/

/-- In the subsingleton case, every form on `Y` is `0`. -/
theorem HolomorphicOneForm.eq_zero_of_subsingleton
    [Subsingleton (HolomorphicOneForm Y)] (α : HolomorphicOneForm Y) :
    α = 0 := Subsingleton.elim α 0

/-- In the subsingleton case, the pointwise pullback is the zero
function. -/
theorem HolomorphicEquiv.pullbackPointwise_eq_zero_of_subsingleton
    (e : HolomorphicEquiv X Y)
    [Subsingleton (HolomorphicOneForm Y)] (α : HolomorphicOneForm Y) :
    e.pullbackPointwise α
      = (fun _ : X => (0 : CotangentSpace (𝓘(ℂ, ℂ)) _)) := by
  rw [HolomorphicOneForm.eq_zero_of_subsingleton α]
  exact HolomorphicEquiv.pullbackPointwise_zero e

/-- **Discharge in the subsingleton case.** When `HolomorphicOneForm
Y` is subsingleton, every form's pullback is realised by the zero
`HolomorphicOneForm X`. -/
theorem isHolomorphicOneFormPullback_of_subsingleton_codomain
    (e : HolomorphicEquiv X Y)
    [Subsingleton (HolomorphicOneForm Y)] (α : HolomorphicOneForm Y) :
    IsHolomorphicOneFormPullback e α := by
  refine ⟨(0 : HolomorphicOneForm X), fun x => ?_⟩
  rw [HolomorphicEquiv.pullbackPointwise_eq_zero_of_subsingleton e α]
  exact HolomorphicOneForm.eval_zero x

/-- **Universal discharge in the subsingleton case.** -/
theorem isHolomorphicOneFormPullback_for_all_of_subsingleton_codomain
    (e : HolomorphicEquiv X Y)
    [Subsingleton (HolomorphicOneForm Y)] :
    IsHolomorphicOneFormPullback_for_all e :=
  fun α => isHolomorphicOneFormPullback_of_subsingleton_codomain e α

/-! ## Specialisation: `Y = RiemannSphere` (unconditional via zz274) -/

/-- **For a biholomorphism `X ≃ RiemannSphere`, every pullback is
realised unconditionally.** Uses zz274's subsingleton instance. -/
theorem isHolomorphicOneFormPullback_for_all_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    IsHolomorphicOneFormPullback_for_all e :=
  isHolomorphicOneFormPullback_for_all_of_subsingleton_codomain e

end JacobianChallenge

end
