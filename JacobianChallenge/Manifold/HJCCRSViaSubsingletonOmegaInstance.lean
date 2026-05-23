/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentFromHolomorphicEquivRS

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` instance under `[Nonempty (HolomorphicEquiv X RS)]`

Combines the Subsingleton-ω-from-biholomorphism chip with the
Subsingleton-ω + BSLB constructor + BSLB transport to produce a HJCC
instance for any X biholomorphic to `RiemannSphere`.

The class `Nonempty (HolomorphicEquiv X RS)` isn't a typeclass per se,
but we can package the implication as a constructor lemma.

## What ships

* `HasJacobianClassicalContent.of_nonemptyHolomorphicEquiv_RS` —
  HJCC X from `Nonempty (HolomorphicEquiv X RiemannSphere)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJCC X from `Nonempty (HolomorphicEquiv X RS)`.** -/
theorem HasJacobianClassicalContent.of_nonemptyHolomorphicEquiv_RS
    (h : Nonempty (HolomorphicEquiv X RiemannSphere)) :
    HasJacobianClassicalContent X := by
  obtain ⟨φ⟩ := h
  exact HasJacobianClassicalContent.of_holomorphicEquiv_RiemannSphere φ

end JacobianChallenge

end
