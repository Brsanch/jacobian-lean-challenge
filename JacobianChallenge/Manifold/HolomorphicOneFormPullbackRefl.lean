/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option diagnostics.threshold 100

/-! # Pullback along the identity biholomorphism is the identity

For the identity biholomorphism `HolomorphicEquiv.refl : HolomorphicEquiv X X`,
the pointwise pullback acts as the identity on `α.eval x`:

  `(refl).pullbackPointwise α x = α.eval x`

This is the unit-of-functoriality identity at the pointwise level. It
combines `mfderiv_id` (mathlib) with `ContinuousLinearMap.comp_id`.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- The underlying function of `HolomorphicEquiv.refl` is the identity. -/
@[simp] theorem HolomorphicEquiv.refl_coe :
    ((HolomorphicEquiv.refl : HolomorphicEquiv X X) : X → X) = id := rfl

/-- **Pullback along the identity is the identity (pointwise).** For
`α : HolomorphicOneForm X` and `x : X`,
`(refl).pullbackPointwise α x = α.eval x`. -/
theorem HolomorphicEquiv.pullbackPointwise_refl
    (α : HolomorphicOneForm X) (x : X) :
    (HolomorphicEquiv.refl : HolomorphicEquiv X X).pullbackPointwise α x
      = HolomorphicOneForm.eval α x := by
  show ContinuousLinearMap.comp (HolomorphicOneForm.eval α x)
      (mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        ((HolomorphicEquiv.refl : HolomorphicEquiv X X) : X → X) x)
    = HolomorphicOneForm.eval α x
  -- Reduce the underlying function to `id`.
  have h_coe :
      ((HolomorphicEquiv.refl : HolomorphicEquiv X X) : X → X) = id :=
    HolomorphicEquiv.refl_coe
  rw [h_coe, mfderiv_id]
  exact ContinuousLinearMap.comp_id _

/-- The pointwise pullback along the identity biholomorphism equals the
underlying section of `α`. -/
theorem HolomorphicEquiv.pullbackPointwise_refl_eq_eval
    (α : HolomorphicOneForm X) :
    (HolomorphicEquiv.refl : HolomorphicEquiv X X).pullbackPointwise α
      = (fun x : X => HolomorphicOneForm.eval α x) := by
  funext x
  exact HolomorphicEquiv.pullbackPointwise_refl α x

end JacobianChallenge

end
