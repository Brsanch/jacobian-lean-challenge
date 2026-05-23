/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PrincipalDivisorAJVanishingGenusZero
import JacobianChallenge.Manifold.JacobiInversionGenusZeroSubsingletonPic0
import JacobianChallenge.Manifold.HasPic0AnalyticEquivFromPhases
import JacobianChallenge.Manifold.MorseSmoothHurewicz

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # `HasPic0AnalyticEquiv X` at `Subsingleton ω + Subsingleton (Pic0 X)` via Phases E + F

Discharges the Phase E and Phase F hypotheses unconditionally at
genus 0 + Subsingleton (Pic0 X), and composes with Phase D hypotheses
(via `hasPic0AnalyticEquiv_of_phases_DEFG`).

In tree at `Subsingleton ω + BSLB`, Phase D is also dischargeable
(via `MorseToSHDPHypothesis.of_subsingleton_omega_of_BSLB`), but it
also needs `MorsePerfectExistsHypothesis X 0` which is genus-0 Morse
function existence on X (not in mathlib at the pin for general X).

This chip exposes the precise gap: at `Subsingleton ω +
Subsingleton (Pic0 X)`, Phases E and F are auto-discharged; Phase D's
Morse-existence half is the remaining open content (genus-0 Morse
function on X).

## What ships

* `hasPic0AnalyticEquiv_of_phases_EF_genus_zero` — HJAE X from Phase
  D's hypotheses + Subsingleton ω + Subsingleton (Pic0 X). Phases E + F
  are auto-discharged this session.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJAE X from Phase D hypotheses + Subsingleton ω + Subsingleton
(Pic0 X).** Phase E and Phase F are auto-discharged at the two
subsingleton hypotheses. -/
theorem hasPic0AnalyticEquiv_of_phases_EF_genus_zero
    [Subsingleton (HolomorphicOneForm X)]
    [Subsingleton (Pic0 X)]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_morse_exists : MorsePerfectExistsHypothesis X (JacobianChallenge.genus X))
    (h_morse_bridge : MorseToSHDPHypothesis (X := X) basis_ω) :
    HasPic0AnalyticEquiv X :=
  hasPic0AnalyticEquiv_of_phases_DEFG X basis_ω h_morse_exists h_morse_bridge
    abelGeneralXHypothesis_of_subsingleton_omega
    jacobiInversionGeneralXHypothesis_of_subsingleton_omega_subsingleton_pic0

end JacobianChallenge

end
