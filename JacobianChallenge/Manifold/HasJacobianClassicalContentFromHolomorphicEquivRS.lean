/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentSubsingleton
import JacobianChallenge.Manifold.BasedSmoothLoopsBoundTransport
import JacobianChallenge.Manifold.HolomorphicEquivGenusInvariance
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere
import JacobianChallenge.Manifold.RiemannSphereGenusFromVanishing

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `HasJacobianClassicalContent X` from a biholomorphism `X ≃ RS`

Composes:
* **Genus invariance** (`HolomorphicEquiv.genus_eq`) — `genus X = 0`.
* **Subsingleton-ω transport** — via `Subsingleton (HolomorphicOneForm RS)`
  + the holomorphic-equivalence (one-forms transport).
* **BSLB transport** (`basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism`) —
  `BSLB RS q₀` → `BSLB X (φ.symm q₀)`.
* **HJCC from Subsingleton ω + BSLB** (this session's
  `HasJacobianClassicalContent.of_subsingleton_and_BSLB`).

## What ships

* `HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere` —
  HJCC X from a biholomorphism `X ≃ RS`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianClassicalContent X` from a biholomorphism `X ≃ RS`.**

Any X biholomorphic to the Riemann sphere has HJCC via:
* `Subsingleton (HolomorphicOneForm X)` transported from RS;
* `BasedSmoothLoopsBoundHypothesis X` transported from RS;
* this session's `_of_subsingleton_and_BSLB` constructor. -/
theorem HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere
    (φ : HolomorphicEquiv X RiemannSphere) :
    HasJacobianClassicalContent X := by
  -- Step 1: genus X = 0 via genus invariance.
  have h_genus : JacobianChallenge.genus X = 0 := by
    rw [HolomorphicEquiv.genus_eq φ]
    exact RiemannSphere.genus_RiemannSphere_eq_zero
  haveI : Subsingleton (HolomorphicOneForm X) := by
    haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
      DiskChartCover.holomorphicOneFormFiniteDim_holds
    rw [JacobianChallenge.genus] at h_genus
    have h_forall : ∀ x : HolomorphicOneForm X, x = 0 :=
      (finrank_zero_iff_forall_zero (K := ℂ) (V := HolomorphicOneForm X)).mp h_genus
    exact ⟨fun a b => (h_forall a).trans (h_forall b).symm⟩
  -- Step 2: BSLB on X at φ.symm q₀ for some q₀ ∈ RS.
  let q₀ : RiemannSphere := Classical.arbitrary _
  have h_bslb_X :
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X
        ((φ.symm : HolomorphicEquiv RiemannSphere X).toEquiv q₀) :=
    basedSmoothLoopsBoundHypothesis_pushforward_biholomorphism
      (φ.symm : HolomorphicEquiv RiemannSphere X) q₀
      (JacobianChallenge.RiemannSphere.basedSmoothLoopsBoundHypothesis_RS_holds q₀)
  -- Step 3: discharge HJCC via the subsingleton-ω + BSLB route.
  exact HasJacobianClassicalContent.of_subsingleton_and_BSLB _ h_bslb_X

end JacobianChallenge

end
