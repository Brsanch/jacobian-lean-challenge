/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquivGenusInvariance
import JacobianChallenge.Manifold.RiemannSphereGenusFromVanishing
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # `Subsingleton (HolomorphicOneForm X)` from a biholomorphism `X ≃ RS`

For any X biholomorphic to `RiemannSphere`,
`HolomorphicOneForm X` is a subsingleton (i.e., `genus X = 0`).

Proof: genus invariance + `genus RS = 0` + finite-dimensionality +
`finrank_zero_iff_forall_zero`.

## What ships

* `subsingleton_holomorphicOneForm_of_holomorphicEquiv_RS` — the theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`Subsingleton (HolomorphicOneForm X)` from a biholomorphism
`X ≃ RS`.** -/
theorem subsingleton_holomorphicOneForm_of_holomorphicEquiv_RS
    (φ : HolomorphicEquiv X RiemannSphere) :
    Subsingleton (HolomorphicOneForm X) := by
  have h_genus : JacobianChallenge.genus X = 0 := by
    rw [HolomorphicEquiv.genus_eq φ]
    exact RiemannSphere.genus_RiemannSphere_eq_zero
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds
  rw [JacobianChallenge.genus] at h_genus
  have h_forall : ∀ x : HolomorphicOneForm X, x = 0 :=
    (finrank_zero_iff_forall_zero (K := ℂ) (V := HolomorphicOneForm X)).mp h_genus
  exact ⟨fun a b => (h_forall a).trans (h_forall b).symm⟩

end JacobianChallenge

end
