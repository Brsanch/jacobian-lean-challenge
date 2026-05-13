/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BijectiveAnalyticToBiholomorphism
import JacobianChallenge.Manifold.GlobalInverseSmooth

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional discharge of `BijectiveAnalyticIsBiholomorphism` (zz388)

The named hypothesis `BijectiveAnalyticIsBiholomorphism X` from
`BijectiveAnalyticToBiholomorphism.lean` is now a **theorem** of `X`,
holding for any compact connected complex 1-manifold `X` modelled on
`ℂ` via `𝓘(ℂ, ℂ)`.

The proof composes the chip arc zz383 → zz384 → zz385 → zz386 → zz387:

* `ContMDiff.contMDiff_invFun_of_bijective` (zz387) gives
  `ContMDiff … ω (Function.invFun f)` from `hf` and `hbij`.
* `Function.leftInverse_invFun hbij.injective` and
  `Function.rightInverse_invFun hbij.surjective` give the two inverse
  identities `LeftInverse / RightInverse (Function.invFun f) f`.
* Together, these data assemble into a `HolomorphicEquiv X Y`, i.e., a
  `Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) X Y ω`.

This closes input #4 of the item-14 six-input split. The remaining
three open inputs (the RR-thread sub-inputs) are blocked on the
documented `linearSystemDeltaP` architectural issue, not on chip-sized
work.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature changes to any pre-existing definition or theorem.
-/

noncomputable section

open scoped Topology Manifold ContDiff

namespace JacobianChallenge

universe u v

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Unconditional discharge of `BijectiveAnalyticIsBiholomorphism X`.**

A bijective `ω`-smooth map between compact connected complex 1-manifolds
is automatically a biholomorphism (`HolomorphicEquiv`). -/
theorem bijectiveAnalyticIsBiholomorphism_holds :
    BijectiveAnalyticIsBiholomorphism.{u, v} X := by
  intro Y _instY1 _instY2 _instY3 _instY4 _instY5 _instY6 f hf hbij
  -- Connected ⇒ Nonempty.
  have : Nonempty X := ConnectedSpace.toNonempty
  -- Both directions are `ω`-smooth.
  have h_inv_smooth :
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω (Function.invFun f) :=
    JacobianChallenge.Manifold.ContMDiff.contMDiff_invFun_of_bijective hf hbij
  -- The underlying equivalence.
  let e : X ≃ Y :=
    { toFun := f
      invFun := Function.invFun f
      left_inv := Function.leftInverse_invFun hbij.injective
      right_inv := Function.rightInverse_invFun hbij.surjective }
  -- Package as `Diffeomorph` (= `HolomorphicEquiv X Y`).
  exact ⟨⟨e, hf, h_inv_smooth⟩⟩

end JacobianChallenge

end
