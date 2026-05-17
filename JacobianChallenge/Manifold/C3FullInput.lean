/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3RewireBundle
import JacobianChallenge.Manifold.AbelJacobiIso
import JacobianChallenge.Manifold.PeriodLatticeDiscretenessFromBilinear

set_option linter.unusedSectionVars false

/-! # C3 full input bundle: all classical inputs for the C3 rewire

The C3 rewire of `JacobianChallenge.Jacobian X` to the analytic Jacobian
requires five **named classical inputs**:

1. `HolomorphicOneFormFiniteDim X` — closed unconditional (item 1, via
   Forster Riesz). Provides a basis `α : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`.
2. `PeriodLatticeDiscretenessBundle (ofSmoothCycle X) α` — Riemann
   bilinear + `H₁(X; ℤ) ≅ ℤ²ᵍ`. Discrete-and-full-rank period lattice
   bundle.
3. `AbelJacobiInput α h` — smooth-path-connectedness base-point bundle.
4. `AbelHypothesis B` — Abel's theorem (principal divisors map to zero).
5. `JacobiInversion B hAbel` — Jacobi inversion (Abel-Jacobi bijective).

With these, `abelJacobiEquiv : Pic⁰ X ≃+ AnalyticJacobian X ...`
upgrades to an additive-group equivalence between the existing Pic⁰
construction and the analytic Jacobian. From there, the rewire of
Basic.lean's manifold instances is mechanical.

This file bundles the four post-item-1 inputs into `C3FullInput X` and
exposes the canonical `abelJacobiEquiv`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology ContDiff
open Module

noncomputable section

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **C3 full input bundle**: aggregates the four named classical inputs
needed for the C3 rewire (post-item-1).

* `basis` — a chosen ℂ-basis of `HolomorphicOneForm X` (available
  unconditionally via item 1 / `Module.finBasis`).
* `discreteness` — Riemann-bilinear + H₁ ≅ ℤ²ᵍ.
* `ajInput` — smooth-path-connectedness base-point bundle.
* `abel` — Abel's theorem.
* `jacobi` — Jacobi inversion.
-/
structure C3FullInput where
  /-- ℂ-basis of `HolomorphicOneForm X`. -/
  basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)
  /-- Discreteness bundle on `(ofSmoothCycle X)`'s period image. -/
  discreteness : PeriodLatticeDiscretenessBundle
    (PeriodPairingData.ofSmoothCycle X) basis
  /-- Smooth-path-connectedness base-point bundle. -/
  ajInput : AbelJacobiInput basis discreteness
  /-- Abel's theorem. -/
  abel : AbelJacobiInput.AbelHypothesis ajInput
  /-- Jacobi inversion. -/
  jacobi : AbelJacobiInput.JacobiInversion ajInput abel

namespace C3FullInput

variable {X}

/-- The Abel-Jacobi `AddEquiv` from the full bundle. -/
noncomputable def abelJacobiEquiv (B : JacobianChallenge.C3FullInput X) :
    Pic0 X ≃+ AnalyticJacobian
      (PeriodPairingData.ofSmoothCycle X) B.basis B.discreteness :=
  B.ajInput.abelJacobiEquiv B.abel B.jacobi

end C3FullInput

end JacobianChallenge

end
