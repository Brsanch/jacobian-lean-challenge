/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackLinearMap
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option diagnostics.threshold 100

/-! # Subsingleton transfer along a `HolomorphicEquiv` (under named smoothness)

This file ships the final reduction for the reverse direction of
challenge item 14: given a biholomorphism `e : X ≃ RS` and the named
universal-smoothness obligation for the pullback along `e.symm`, we
deduce `Subsingleton (HolomorphicOneForm X)`. Composing with zz277/278
this collapses `S2ImpliesGenus0 X` unconditionally for any `X`
biholomorphic to the Riemann sphere.

## The deduction

Suppose `α : HolomorphicOneForm X`. The pullback along `e.symm : RS → X`
gives a `HolomorphicOneForm RS` (under the named smoothness obligation).
But every form on RS is zero (zz274). So the pointwise pullback is
identically zero. At `y = e x` this gives
`(α.eval x).comp (mfderiv e.symm (e x)) = 0`. The map
`mfderiv e.symm (e x)` has a left inverse `mfderiv e x` (chain rule on
`e.symm ∘ e = id`), so `α.eval x = 0`. Therefore `α = 0`.

## Named smoothness obligation (single remaining input)

`IsHolomorphicOneFormPullback_for_all (e.symm : HolomorphicEquiv RS X)`.

This is the analytic content that the pointwise pullback of every form
on `X` along the inverse biholomorphism `e.symm` is realised by a
genuine `HolomorphicOneForm RS`. Discharging it requires the
cotangent-bundle transition machinery in
`Manifold/CotangentPullbackBridge.lean`.

## What this file delivers

* `mfderiv_symm_comp_mfderiv_self_holomorphicEquiv` —
  `(mfderiv e.symm (e x)) ∘L (mfderiv e x) = id` for `e :
  HolomorphicEquiv X Y`.
* `pullbackPointwise_eq_zero_apply_on_image` — if the pointwise
  pullback along `e.symm` of `α` vanishes everywhere, then `α.eval x =
  0` for every `x`.
* `subsingleton_HolomorphicOneForm_of_pullback_smoothness_RiemannSphere`
  — the headline subsingleton-transfer theorem.
* `subsingleton_HolomorphicOneForm_of_holomorphicEquiv_RiemannSphere`
  — same in the form `(hSmooth : IsHolomorphicOneFormPullback_for_all
  e.symm) → Subsingleton (HolomorphicOneForm X)`.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]

/-! ## Chain rule for `HolomorphicEquiv`

`(mfderiv e.symm (e x)) ∘L (mfderiv e x) = id`. -/

/-- `ω ≠ 0` as a `WithTop ℕ∞`. -/
private theorem analytic_ne_zero : (ω : WithTop ℕ∞) ≠ 0 := by
  intro h
  exact absurd h (by decide)

/-- Every `HolomorphicEquiv` is `MDifferentiableAt` at every point. -/
theorem HolomorphicEquiv.mdifferentiableAt
    (e : HolomorphicEquiv X Y) (x : X) :
    MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e : X → Y) x :=
  (e.contMDiff_forward x).mdifferentiableAt analytic_ne_zero

/-- The inverse of a `HolomorphicEquiv` is also `MDifferentiableAt`. -/
theorem HolomorphicEquiv.mdifferentiableAt_symm
    (e : HolomorphicEquiv X Y) (y : Y) :
    MDifferentiableAt (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
      (e.toEquiv.symm : Y → X) y :=
  (e.contMDiff_inverse y).mdifferentiableAt analytic_ne_zero

/-- `e.symm ∘ e = id` as functions. -/
theorem HolomorphicEquiv.symm_comp_self
    (e : HolomorphicEquiv X Y) :
    (e.toEquiv.symm : Y → X) ∘ (e.toEquiv : X → Y) = id := by
  funext x
  exact e.toEquiv.symm_apply_apply x

/-- **Chain-rule identity for `HolomorphicEquiv`.** The composition of
`mfderiv e.symm` at `e x` with `mfderiv e` at `x` is the identity. -/
theorem HolomorphicEquiv.mfderiv_symm_comp_mfderiv_self
    (e : HolomorphicEquiv X Y) (x : X) :
    (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.toEquiv.symm : Y → X) (e x)).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.toEquiv : X → Y) x)
      = ContinuousLinearMap.id ℂ (TangentSpace (𝓘(ℂ, ℂ)) x) := by
  have h_comp_eq :
      mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          ((e.toEquiv.symm : Y → X) ∘ (e.toEquiv : X → Y)) x
        = (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              (e.toEquiv.symm : Y → X) (e x)).comp
            (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              (e.toEquiv : X → Y) x) := by
    refine mfderiv_comp x ?_ ?_
    · exact e.mdifferentiableAt_symm (e x)
    · exact e.mdifferentiableAt x
  rw [← h_comp_eq, e.symm_comp_self]
  exact mfderiv_id

/-! ## The subsingleton transfer

Under the named smoothness obligation for the inverse-direction pullback,
deduce `Subsingleton (HolomorphicOneForm X)` from `Subsingleton
(HolomorphicOneForm Y)`. -/

variable (e : HolomorphicEquiv X Y)

/-- **Vanishing-of-pullback transfer.** If for every `α :
HolomorphicOneForm X`, the pointwise pullback along `e.symm` is the
underlying section of some `pα : HolomorphicOneForm Y`, *and* every
form on `Y` is zero, then every form on `X` is zero. -/
theorem HolomorphicOneForm.eq_zero_of_pullback_smoothness_subsingleton_target
    [Subsingleton (HolomorphicOneForm Y)]
    (hSmooth : IsHolomorphicOneFormPullback_for_all e.symm)
    (α : HolomorphicOneForm X) :
    α = 0 := by
  -- Show α.eval x = 0 for all x; then `α = 0` by section extensionality.
  refine ContMDiffSection.coe_injective ?_
  funext x
  -- Get the pullback witness for α.
  obtain ⟨pα, hpα⟩ := hSmooth α
  -- pα is in the subsingleton target, so pα = 0.
  have h_pα_zero : pα = 0 := Subsingleton.elim pα 0
  -- Therefore pα.eval y = 0 for all y.
  have h_pα_eval_zero : ∀ y : Y, HolomorphicOneForm.eval pα y = 0 := by
    intro y; rw [h_pα_zero, HolomorphicOneForm.eval_zero]
  -- Combine with hpα: pointwise pullback at y equals pα.eval y, which is 0.
  have h_pull_zero : ∀ y : Y, e.symm.pullbackPointwise α y = 0 := by
    intro y; rw [← hpα y]; exact h_pα_eval_zero y
  -- Specialise at y = e x to get α.eval x ∘L mfderiv e.symm (e x) = 0.
  have h_at_ex :
      ContinuousLinearMap.comp (HolomorphicOneForm.eval α (e.symm (e x)))
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            (e.symm.toEquiv : Y → X) (e x)) = 0 := by
    have := h_pull_zero (e x)
    -- Unfold pullbackPointwise.
    show ContinuousLinearMap.comp (HolomorphicOneForm.eval α (e.symm (e x)))
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
          (e.symm.toEquiv : Y → X) (e x)) = 0
    show e.symm.pullbackPointwise α (e x) = 0
    exact this
  -- Use e.symm (e x) = x.
  have h_symm_apply : (e.symm : Y → X) (e x) = x := by
    show e.toEquiv.symm (e.toEquiv x) = x
    exact e.toEquiv.symm_apply_apply x
  rw [h_symm_apply] at h_at_ex
  -- Compose with mfderiv e x. Use the chain-rule identity.
  -- (α.eval x ∘L D) ∘L D' = α.eval x ∘L (D ∘L D'). We use D' = mfderiv e x
  -- and D ∘L D' = id, so the result is α.eval x = 0.
  have h_chain : (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e.symm.toEquiv : Y → X) (e x)).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.toEquiv : X → Y) x)
      = ContinuousLinearMap.id ℂ (TangentSpace (𝓘(ℂ, ℂ)) x) := by
    -- This is the chain-rule for HolomorphicEquiv (symm version).
    -- e.symm.toEquiv = e.toEquiv.symm definitionally.
    show (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (e.toEquiv.symm : Y → X) (e x)).comp
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.toEquiv : X → Y) x)
      = ContinuousLinearMap.id ℂ (TangentSpace (𝓘(ℂ, ℂ)) x)
    exact e.mfderiv_symm_comp_mfderiv_self x
  -- Show α.eval x = 0 by evaluating pointwise on tangent vectors.
  have h_eval_zero : HolomorphicOneForm.eval α x = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    -- Compose h_at_ex with `mfderiv e x v` on the right.
    have h_apply :
        ((HolomorphicOneForm.eval α x).comp
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            (e.symm.toEquiv : Y → X) (e x)))
          (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) (e.toEquiv : X → Y) x v) = 0 := by
      rw [h_at_ex]; rfl
    rw [ContinuousLinearMap.comp_apply] at h_apply
    -- The inner expression `mfderiv e.symm (e x) (mfderiv e x v) = id v = v`.
    have h_chain_apply :
        (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
            (e.symm.toEquiv : Y → X) (e x))
            ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
              (e.toEquiv : X → Y) x) v) = v := by
      have := congrArg (fun f : TangentSpace (𝓘(ℂ, ℂ)) x →L[ℂ]
            TangentSpace (𝓘(ℂ, ℂ)) x => f v) h_chain
      simpa [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using this
    show HolomorphicOneForm.eval α x v = (0 : ℂ →L[ℂ] ℂ) v
    rw [ContinuousLinearMap.zero_apply]
    -- h_apply : α.eval x (D2 (D1 v)) = 0; h_chain_apply : D2 (D1 v) = v.
    -- Combine via the rewrite of the inner expression.
    calc HolomorphicOneForm.eval α x v
        = HolomorphicOneForm.eval α x
            ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
                (e.symm.toEquiv : Y → X) (e x))
              ((mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
                  (e.toEquiv : X → Y) x) v)) := by
              rw [h_chain_apply]
      _ = 0 := h_apply
  show HolomorphicOneForm.eval α x = HolomorphicOneForm.eval 0 x
  rw [HolomorphicOneForm.eval_zero]
  exact h_eval_zero

/-- **Subsingleton transfer from `Y` to `X`.** Under the named
smoothness obligation, `HolomorphicOneForm X` is subsingleton whenever
`HolomorphicOneForm Y` is. -/
theorem HolomorphicOneForm.subsingleton_of_pullback_smoothness
    [Subsingleton (HolomorphicOneForm Y)]
    (hSmooth : IsHolomorphicOneFormPullback_for_all e.symm) :
    Subsingleton (HolomorphicOneForm X) := by
  refine ⟨fun α β => ?_⟩
  have hα : α = 0 :=
    HolomorphicOneForm.eq_zero_of_pullback_smoothness_subsingleton_target
      e hSmooth α
  have hβ : β = 0 :=
    HolomorphicOneForm.eq_zero_of_pullback_smoothness_subsingleton_target
      e hSmooth β
  rw [hα, hβ]

/-! ## Specialisation to `Y = RiemannSphere` (unconditional in the target side) -/

/-- **Headline.** For any biholomorphism `e : HolomorphicEquiv X RS`,
the named smoothness obligation for the inverse-direction pullback
(`IsHolomorphicOneFormPullback_for_all e.symm`) suffices to deduce
`Subsingleton (HolomorphicOneForm X)`. The Riemann-sphere subsingleton
instance is supplied by zz274. -/
theorem HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (hSmooth : IsHolomorphicOneFormPullback_for_all e.symm) :
    Subsingleton (HolomorphicOneForm X) :=
  HolomorphicOneForm.subsingleton_of_pullback_smoothness e hSmooth

/-- **Genus consequence.** Under the named smoothness obligation,
`HolomorphicEquiv X RiemannSphere` forces `genus X = 0`. -/
theorem JacobianChallenge.genus_eq_zero_of_holomorphicEquiv_RiemannSphere
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (hSmooth : IsHolomorphicOneFormPullback_for_all e.symm) :
    JacobianChallenge.genus X = 0 := by
  haveI := HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere
    e hSmooth
  exact genus_eq_zero_of_holomorphicOneForm_subsingleton X inferInstance

end JacobianChallenge

end
