/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPic0

set_option linter.unusedSectionVars false

/-! # General-X Abel + Jacobi-inversion hypotheses (Phases E, F)

Phase E and Phase F of the item-5 closure plan are about discharging:

* **Phase E (Abel's theorem at general X):** `AbelHypothesis B` for
  every `B : AbelJacobiInput α h` on any compact connected Riemann
  surface `X`. The general-X analog of the in-tree
  `TLDivSumHypothesis L` (for T_L only). Classical content: ∮ d log f
  = 0 on a compact Riemann surface via residue theorem.

* **Phase F (Jacobi inversion / Abel converse at general X):**
  surjectivity of `B.abelJacobi hAbel : Pic⁰ X →+ AnalyticJacobian`
  for any `B, hAbel`. Classical content: Riemann theta functions on
  the analytic Jacobian.

This file names them as `Prop`s. The actual discharges are
multi-week classical-content ports (residue theorem, theta functions)
not in mathlib at the pin.

## What this file ships

* `AbelGeneralXHypothesis X` — quantifies Abel over all `(α, h, B)`
  on `X`. Phase E's open content.
* `JacobiInversionGeneralXHypothesis X` — quantifies Jacobi inversion
  over all `(α, h, B, hAbel)` on `X`. Phase F's open content.

Combined with Phase D's two hypotheses (`MorsePerfectExistsHypothesis`
and `MorseToSHDPHypothesis`), these complete the named-hypothesis
factorization of the item-5 closure plan.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Phase E — Abel's theorem at general X.**

For every choice of `(α, h, B)`, the Abel hypothesis holds: the
descent of `B.abelJacobiDiv0Hom` through `Pic⁰` (via
`QuotientAddGroup.lift`) is well-defined because `B.abelJacobiDiv0Hom`
vanishes on the principal-divisor subgroup.

This is the classical Abel theorem on a compact connected Riemann
surface, generalising `TLDivSumHypothesis L` (which discharges this on
`X = ℂ ⧸ L`). Open content: residue theorem on a compact Riemann
surface plus the path-representation of principal divisors. -/
def AbelGeneralXHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInput α h),
    AbelJacobiInput.AbelHypothesis B

/-- **Phase F — Jacobi inversion / Abel converse at general X.**

For every `B, hAbel`, the descended `B.abelJacobi hAbel : Pic⁰ X →+
AnalyticJacobian ...` is surjective. Equivalently: every element of
the analytic Jacobian is the Abel-Jacobi image of some degree-zero
divisor.

This is the classical Jacobi inversion theorem, generalising
`TLAbelConverseHypothesis L` (which discharges this on `X = ℂ ⧸ L`
via Weierstrass-σ). Open content: Riemann theta function on the
analytic Jacobian + the theta divisor. -/
def JacobiInversionGeneralXHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeDiscretenessBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInput α h)
    (hAbel : AbelJacobiInput.AbelHypothesis B),
    Function.Surjective (B.abelJacobi hAbel)

end JacobianChallenge

end
