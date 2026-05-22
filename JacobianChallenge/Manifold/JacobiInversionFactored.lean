/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneralXHypotheses

set_option linter.unusedSectionVars false

/-! # Phase F factored into Abel-converse + surjectivity (Frontier-3)

Phase F's `JacobiInversionGeneralXHypothesis X` packages two
classically-distinct theorems:

* **Abel's converse** (injectivity of `abelJacobi`): if a divisor's
  Abel-Jacobi image is the zero class in the analytic Jacobian, then
  the divisor is principal.

* **Jacobi inversion** (surjectivity of `abelJacobi`): every element
  of the analytic Jacobian is realised by some Div⁰ class — classically
  via Riemann theta functions.

Both are needed to make `B.abelJacobi hAbel` a bijection (an
`AddEquiv`). This file factors them as separate Props so future
discharges can attack each independently — they involve different
classical content.

## What this file ships

* `AbelConverseGeneralXHypothesis X` — injectivity quantified.
* `JacobiInversionSurjectiveGeneralXHypothesis X` — surjectivity
  quantified.
* `jacobiInversionGeneralXHypothesis_of_factors` — bridge: the two
  factors combine to give the full
  `JacobiInversionGeneralXHypothesis X`.

## Why factoring matters

The classical proofs of Abel converse and Jacobi inversion are
genuinely different:

* **Abel converse** classically uses the abelJacobiDiv0Hom kernel
  description plus the fact that an integral with vanishing periods
  is exact. Heavy use of the residue theorem on `d log f`.

* **Jacobi inversion** classically uses Riemann's theta function
  `ϑ(z; Ω) = ∑_{n ∈ ℤ^g} exp(πi nᵀΩn + 2πi nᵀz)`. The theta divisor
  `(ϑ) ⊂ J(X)` parametrises Div^{g-1} via Abel-Jacobi; a translate
  recovers Div^0. This is a different chunk of classical content.

Factoring them lets each be discharged in its own time.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Abel's converse at general X.** Injectivity of `B.abelJacobi
hAbel`: if a degree-zero divisor's Abel-Jacobi value vanishes in the
analytic Jacobian, then the divisor is principal.

Classical content: a meromorphic 1-form is exact (= `d log f` for some
f) iff its period vector is in the period lattice. -/
def AbelConverseGeneralXHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInputSymp α h)
    (hAbel : AbelJacobiInputSymp.AbelHypothesis B),
    Function.Injective (B.abelJacobi hAbel)

/-- **Jacobi inversion (surjectivity) at general X.** Every element
of the analytic Jacobian is `B.abelJacobi hAbel [D]` for some
`D : Div⁰ X`.

Classical content: the Riemann theta function `ϑ(z; Ω)` + the theta
divisor construction. -/
def JacobiInversionSurjectiveGeneralXHypothesis : Prop :=
  ∀ (α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α)
    (B : AbelJacobiInputSymp α h)
    (hAbel : AbelJacobiInputSymp.AbelHypothesis B),
    Function.Surjective (B.abelJacobi hAbel)

/-- **Bridge: the two factors give Phase F.** Combining injectivity
(Abel converse) and surjectivity (Jacobi inversion) gives the full
`JacobiInversionGeneralXHypothesis X`. -/
theorem jacobiInversionGeneralXHypothesis_of_factors
    (h_inj : AbelConverseGeneralXHypothesis X)
    (h_surj : JacobiInversionSurjectiveGeneralXHypothesis X) :
    JacobiInversionGeneralXHypothesis X := by
  intro α h_symp B hAbel
  exact {
    injective := h_inj α h_symp B hAbel
    surjective := h_surj α h_symp B hAbel }

end JacobianChallenge

end
