/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquivFromPhasesEF
import JacobianChallenge.Manifold.PhaseEFSubsingletonOmega

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # HasPic0AnalyticEquiv at subsingleton ω + Pic⁰ via Phase E/F + G route

Composes Frontier-4 (Phase E + F discharged at subsingleton ω + Pic⁰)
with Frontier-5 (Phase G modulo SHDP) to give a Phase-G-route
discharge of `HasPic0AnalyticEquiv X` at the subsingleton hypotheses.

This is an **alternative route** to Phase A's `bonus` chip (which
uses a direct subsingleton AddEquiv construction). The two routes
produce the same conclusion via different proof chains:

* **Phase A bonus**: subsingleton ω + Pic⁰ + SHDP ⟹
  `HasPic0AnalyticEquiv X` via `addEquivOfSubsingletons` (direct).

* **This file** (Phase E/F + G route): same hypotheses ⟹
  `HasPic0AnalyticEquiv X` via the full Phase E (Abel) + Phase F
  (Jacobi inversion) + Phase G (abelJacobiEquiv composition) chain,
  each leg's hypothesis dischargeable at subsingleton.

The second route is structurally important because it **exercises the
full Phase G machinery** on a concrete case — validating that the
named-hypothesis factorization actually composes to the conclusion.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HasPic0AnalyticEquiv at subsingleton ω + Pic⁰ via the Phase E/F + G route.**

Combines:
* Frontier-4's `abelGeneralXHypothesis_of_subsingleton_omega` (Phase E).
* Frontier-4's `jacobiInversionGeneralXHypothesis_of_subsingleton_omega_pic0`
  (Phase F).
* Frontier-5's `hasPic0AnalyticEquiv_of_phases_EF` (Phase G modulo SHDP).

The three hypotheses (subsingleton ω, subsingleton Pic⁰, SHDP) match
Phase A's `bonus` chip exactly, so this is an alternative proof of
the same conclusion via the full Phase E/F/G chain. -/
theorem hasPic0AnalyticEquiv_of_subsingleton_omega_pic0_via_phases
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)]
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    HasPic0AnalyticEquiv X :=
  hasPic0AnalyticEquiv_of_phases_EF X basis_ω
    abelGeneralXHypothesis_of_subsingleton_omega
    jacobiInversionGeneralXHypothesis_of_subsingleton_omega_pic0

end JacobianChallenge

end
