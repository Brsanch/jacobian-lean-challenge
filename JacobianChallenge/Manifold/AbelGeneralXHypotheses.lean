/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPic0
import JacobianChallenge.Manifold.AbelJacobiIso
import JacobianChallenge.Manifold.C3FullInputSymp

set_option linter.unusedSectionVars false

/-! # General-X Abel + Jacobi-inversion hypotheses (Phases E, F)

Phase E and Phase F of the item-5 closure plan are about discharging:

* **Phase E (Abel's theorem at general X):** `AbelHypothesis B` for
  every `B : AbelJacobiInputSymp α h` on any compact connected Riemann
  surface `X`. The general-X analog of the in-tree
  `TLDivSumHypothesis L` (for T_L only). Classical content: ∮ d log f
  = 0 on a compact Riemann surface via residue theorem.

* **Phase F (Jacobi inversion / Abel converse at general X):**
  `JacobiInversion B hAbel` (injectivity + surjectivity of
  `B.abelJacobi hAbel`). Classical content: Riemann theta functions on
  the analytic Jacobian.

This file names them as `Prop`s using the **symplectic** parallel of
the Abel-Jacobi chain (`AbelJacobiInputSymp` against
`PeriodLatticeSymplecticBundle`), which is the variant the in-tree T_L
case and `CanonicalAnalyticJacobian` use. The non-symplectic
`AbelJacobiInput / PeriodLatticeDiscretenessBundle` parallel has the
over-strong `Basis (Fin 2g) ℤ data.H1` requirement (since
`data.H1 = SmoothCycle X` is infinite-dimensional, that bundle is
generically impossible to construct).

The actual discharges are multi-week classical-content ports (residue
theorem, theta functions) not in mathlib at the pin.

## What this file ships

* `AbelGeneralXHypothesis X` — quantifies Abel over all `(α, h, B)`
  on `X` (symplectic). Phase E's open content.
* `JacobiInversionGeneralXHypothesis X` — quantifies Jacobi inversion
  over all `(α, h, B, hAbel)` on `X` (symplectic). Phase F's open
  content.

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

/-- **Phase E — Abel's theorem at general X (symplectic).**

For every choice of `(α, h, B)`, the symplectic Abel hypothesis holds:
the descent of `B.abelJacobiDiv0Hom` through `Pic⁰` (via
`QuotientAddGroup.lift`) is well-defined because `B.abelJacobiDiv0Hom`
vanishes on the principal-divisor subgroup.

Generalises `TLDivSumHypothesis L` (which discharges this on
`X = ℂ ⧸ L`). Open content: residue theorem on a compact Riemann
surface plus the path-representation of principal divisors. -/
def AbelGeneralXHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInputSymp α h),
    AbelJacobiInputSymp.AbelHypothesis B

/-- **Phase F — Jacobi inversion / Abel converse at general X
(symplectic).**

For every `B, hAbel`, the descended `B.abelJacobi hAbel : Pic⁰ X →+
AnalyticJacobianSymp ...` is a bijection (the
`AbelJacobiInputSymp.JacobiInversion` structure carries both
injectivity = Abel's converse and surjectivity = classical Jacobi
inversion).

Generalises `TLAbelConverseHypothesis L`. Open content:
* Injectivity (Abel converse): if a Div⁰'s period vector is in the
  period lattice, the divisor is principal.
* Surjectivity (Jacobi inversion): Riemann theta function + the
  theta divisor. -/
def JacobiInversionGeneralXHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInputSymp α h)
    (hAbel : AbelJacobiInputSymp.AbelHypothesis B),
    AbelJacobiInputSymp.JacobiInversion B hAbel

end JacobianChallenge

end
