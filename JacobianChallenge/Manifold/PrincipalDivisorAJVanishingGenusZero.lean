/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelGeneralXFromPrincipalGenerators
import JacobianChallenge.Manifold.CanonicalAnalyticJacobianSubsingleton

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # `PrincipalDivisorAJVanishingHypothesis X` UNCONDITIONAL at genus 0

At `Subsingleton (HolomorphicOneForm X)` (i.e., `genus X = 0`), the
`AnalyticJacobianSymp` is a subsingleton (the period-lattice quotient
of `Fin 0 → ℂ`). So **every** value of `B.abelJacobiDivHom` is `0`,
in particular `B.abelJacobiDivHom (principalDivisorMap f) = 0` for
all `f`. Hence `PrincipalDivisorAJVanishingHypothesis X` is
unconditional at genus 0.

Combined with `abelGeneralXHypothesis_of_principalDivisorAJVanishing`,
`AbelGeneralXHypothesis X` is **unconditional at genus 0** on every
compact connected complex 1-manifold.

## What ships

* `principalDivisorAJVanishing_of_subsingleton_omega` — the atomic
  vanishing at genus 0.
* `abelGeneralXHypothesis_of_subsingleton_omega` — `AbelGeneralXHypothesis X`
  unconditional at genus 0 via composition.

## Significance

Discharges Phase E (Abel's theorem at general X) at genus 0
unconditionally. The chain:
* genus 0 → AnalyticJacobianSymp subsingleton (in tree);
* subsingleton target → all map values equal 0;
* `PrincipalDivisorAJVanishing → AbelGeneralXHypothesis` (in tree).

For genus ≥ 1, Abel's theorem requires deep Stokes content.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`PrincipalDivisorAJVanishingHypothesis X` UNCONDITIONAL at
genus 0.** -/
theorem principalDivisorAJVanishing_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] :
    PrincipalDivisorAJVanishingHypothesis X := by
  intro α h_symp B f
  -- Under Subsingleton ω, AnalyticJacobianSymp is subsingleton.
  haveI : Subsingleton (Fin (JacobianChallenge.genus X) → ℂ) := by
    have : JacobianChallenge.genus X = 0 := Module.finrank_zero_of_subsingleton
    rw [this]; exact Pi.uniqueOfIsEmpty _ |>.instSubsingleton
  haveI : Subsingleton (AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle X) α h_symp) :=
    subsingleton_jacobianOfLattice_of_subsingleton_ambient _
  exact Subsingleton.elim _ _

/-- **`AbelGeneralXHypothesis X` UNCONDITIONAL at genus 0.** -/
theorem abelGeneralXHypothesis_of_subsingleton_omega
    [Subsingleton (HolomorphicOneForm X)] :
    AbelGeneralXHypothesis X :=
  abelGeneralXHypothesis_of_principalDivisorAJVanishing X
    principalDivisorAJVanishing_of_subsingleton_omega

end JacobianChallenge

end
