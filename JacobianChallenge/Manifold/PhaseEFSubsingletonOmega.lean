/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneralXHypotheses
import JacobianChallenge.Manifold.JacobiInversionFactored
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton

set_option linter.unusedSectionVars false

/-! # Phase E + F discharged at subsingleton ω (Frontier-4)

When `[Subsingleton (HolomorphicOneForm X)]` (genus 0) — and hence both
`Pic⁰ X` and `AnalyticJacobianSymp _ _ _` are subsingleton — Phases E
and F are **trivially discharged**:

* Phase E (`AbelGeneralXHypothesis`): `B.abelJacobiDiv0Hom D` lives in
  a subsingleton AnalyticJacobian, so it must equal `0`. Hence Abel.
* Phase F injective (`AbelConverseGeneralXHypothesis`): the source
  `Pic⁰ X` is subsingleton, so any map out of it is trivially injective.
* Phase F surjective (`JacobiInversionSurjectiveGeneralXHypothesis`):
  the target is subsingleton, so any map into it is trivially
  surjective.

This is the genus-0 universal discharge of Phases E and F, completing
the genus-0 chain (together with Phase A's subsingleton-omega
discharge of `HasPic0AnalyticEquiv`).

## What this file ships

* `abelGeneralXHypothesis_of_subsingleton_omega` — Phase E
  discharged at subsingleton ω.
* `abelConverseGeneralXHypothesis_of_subsingleton_pic0` — Phase F
  injectivity discharged at subsingleton Pic⁰ (e.g., at genus 0 on RS).
* `jacobiInversionSurjectiveGeneralXHypothesis_of_subsingleton_omega`
  — Phase F surjectivity discharged at subsingleton ω.
* `jacobiInversionGeneralXHypothesis_of_subsingleton_omega_pic0` —
  full Phase F discharged at the combined subsingleton hypotheses.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Phase E discharged at subsingleton ω.** When `[Subsingleton
(HolomorphicOneForm X)]`, the analytic Jacobian is subsingleton, so
`B.abelJacobiDiv0Hom D` is trivially `0` for all D. -/
theorem abelGeneralXHypothesis_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] :
    AbelGeneralXHypothesis X := by
  intro α h_symp B D _
  -- AnalyticJacobianSymp _ α h_symp is subsingleton at genus 0.
  -- Subsingleton ω + DiskChartCover finite-dim ⇒ genus = 0 ⇒ Fin g → ℂ subsingleton
  -- ⇒ JacobianOfLattice subsingleton.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_finGenusToComplex_of_subsingleton_omega
  haveI : Subsingleton (AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle X) α h_symp) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient _
  exact Subsingleton.elim _ _

/-- **Phase F injectivity discharged at subsingleton Pic⁰.** When
`[Subsingleton (Pic0 X)]`, any function out of `Pic⁰ X` is trivially
injective. -/
theorem abelConverseGeneralXHypothesis_of_subsingleton_pic0
    [Subsingleton (Pic0 X)] :
    AbelConverseGeneralXHypothesis X := by
  intro α h_symp B hAbel a b _
  exact Subsingleton.elim _ _

/-- **Phase F surjectivity discharged at subsingleton ω.** When
`[Subsingleton (HolomorphicOneForm X)]`, the analytic Jacobian is
subsingleton, so any function into it is trivially surjective. -/
theorem jacobiInversionSurjectiveGeneralXHypothesis_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] :
    JacobiInversionSurjectiveGeneralXHypothesis X := by
  intro α h_symp B hAbel y
  -- Pick any element of the source.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) :=
    subsingleton_finGenusToComplex_of_subsingleton_omega
  haveI : Subsingleton (AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle X) α h_symp) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient _
  exact ⟨0, Subsingleton.elim _ _⟩

/-- **Full Phase F discharged at the combined subsingleton hypotheses.**
Combines injectivity (from subsingleton Pic⁰) and surjectivity (from
subsingleton ω) into the full `JacobiInversionGeneralXHypothesis X`. -/
theorem jacobiInversionGeneralXHypothesis_of_subsingleton_omega_pic0
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)] :
    JacobiInversionGeneralXHypothesis X :=
  jacobiInversionGeneralXHypothesis_of_factors X
    abelConverseGeneralXHypothesis_of_subsingleton_pic0
    jacobiInversionSurjectiveGeneralXHypothesis_of_subsingleton_omega

end JacobianChallenge

end
