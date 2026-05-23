/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobiInversionSurjectivityGenusZero
import JacobianChallenge.Manifold.AbelGeneralXHypotheses

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Phase F (JacobiInversionGeneralXHypothesis) at genus 0 + Subsingleton (Pic0 X)

Composes the genus-0 surjectivity chip with a `[Subsingleton (Pic0 X)]`
hypothesis to discharge `JacobiInversion B hAbel` (the full structure
= injectivity + surjectivity) unconditionally at genus 0 + trivial
Pic0.

Combined with the earlier `abelGeneralXHypothesis_of_subsingleton_omega`,
this gives `JacobiInversionGeneralXHypothesis X` at
`[Subsingleton (HolomorphicOneForm X)] + [Subsingleton (Pic0 X)]`.

For RS, both hypotheses fire unconditionally; for any X biholomorphic
to RS, both follow from the in-tree biholomorphism transport
(Subsingleton ω chip from this session + Pic0-functorial transport TBD).

## What ships

* `jacobiInversion_of_subsingleton_omega_subsingleton_pic0` — both
  halves of Jacobi inversion at the two-subsingleton hypothesis.
* `jacobiInversionGeneralXHypothesis_of_subsingleton_omega_subsingleton_pic0`
  — the Phase F top-level Prop discharged.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace AbelJacobiInputSymp

/-- **Full Jacobi inversion at `[Subsingleton ω] + [Subsingleton (Pic0 X)]`.** -/
theorem jacobiInversion_of_subsingleton_omega_subsingleton_pic0
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)]
    {α : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h : PeriodLatticeSymplecticBundle (PeriodPairingData.ofSmoothCycle X) α}
    (B : AbelJacobiInputSymp α h) (hAbel : AbelHypothesis B) :
    JacobiInversion B hAbel where
  injective := by
    intro a b _
    exact Subsingleton.elim _ _
  surjective := abelJacobi_surjective_of_subsingleton_omega B hAbel

end AbelJacobiInputSymp

/-- **Phase F (`JacobiInversionGeneralXHypothesis`) UNCONDITIONAL under
`[Subsingleton ω] + [Subsingleton (Pic0 X)]`.** -/
theorem jacobiInversionGeneralXHypothesis_of_subsingleton_omega_subsingleton_pic0
    [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)] :
    JacobiInversionGeneralXHypothesis X := by
  intro α h B hAbel
  exact AbelJacobiInputSymp.jacobiInversion_of_subsingleton_omega_subsingleton_pic0
    (X := X) (α := α) (h := h) B hAbel

end JacobianChallenge

end
