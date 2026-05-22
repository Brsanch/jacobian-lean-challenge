/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MorseSmoothHurewicz
import JacobianChallenge.Manifold.SmoothHomologyDataPackageSubsingleton
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass

set_option linter.unusedSectionVars false

/-! # Discharges of `MorseToSHDPHypothesis` at concrete conditions

Concrete substantive discharges of the **Phase D-3 bridge hypothesis**
`MorseToSHDPHypothesis basis_ω` (`Manifold/MorseSmoothHurewicz.lean`
line 81). This is one of the four atomic open named hypotheses
remaining after Phases A-G + Frontier-1..4 land. This file ships:

* `morseToSHDPHypothesis_of_subsingleton_omega_of_BSLB` — at
  `Subsingleton (HolomorphicOneForm X)` + a chosen `basePoint` and
  `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint`,
  `MorseToSHDPHypothesis basis_ω` is unconditionally dischargeable.
  Factors through
  `nonempty_smoothHomologyDataPackage_of_subsingleton_and_BSLB`.

* `morseToSHDPHypothesis_RiemannSphere` — **unconditional** on
  `RiemannSphere` at any `basis_ω`. Subsingleton ω holds (genus 0) and
  BSLB on RS is unconditional, so SHDP is in tree.

* `morseToSHDPHypothesis_complexTorus` — **unconditional** on
  `T_L = ℂ ⧸ L` at `basis_g_dz L`. SHDP at genus 1 is in tree.

## Why this matters

`MorseToSHDPHypothesis basis_ω` is one of the **two Phase-D named
hypotheses** in the genus-`g` joint composition
`hasPic0AnalyticEquiv_of_phases_DEFG`. Discharging it
unconditionally on RS and T_L closes Phase D's contribution on those
two specific X, validating the architecture end-to-end at genus 0 and
genus 1. At general subsingleton-ω X (genus 0), the Morse data is
*ignored* — the conclusion is supplied directly by the existing
subsingleton-ω + BSLB SHDP discharge, with the perfect-Morse
hypothesis irrelevant to the SHDP construction. (The Morse data IS
relevant at general genus, where the CW decomposition is what
furnishes the BSLB-replacing Hurewicz content — but at subsingleton ω
the BSLB-equivalent is the only remaining content.)

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Discharge at `Subsingleton ω` + a BSLB witness -/

/-- **`MorseToSHDPHypothesis basis_ω`** at `Subsingleton (HolomorphicOneForm X)` +
`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint`.

At subsingleton ω the genus is `0`, so the symplectic-basis tuple is
empty, the bilinear-LI condition is vacuous, and the Hurewicz
condition on the empty basis collapses to BSLB at the chosen base
point. The Morse data is irrelevant. -/
theorem morseToSHDPHypothesis_of_subsingleton_omega_of_BSLB
    [Subsingleton (HolomorphicOneForm X)]
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (basePoint : X)
    (h_BSLB : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X basePoint) :
    MorseToSHDPHypothesis basis_ω := by
  intro _ _ _
  exact nonempty_smoothHomologyDataPackage_of_subsingleton_and_BSLB
    basis_ω basePoint h_BSLB

/-! ## RS unconditional discharge -/

namespace RiemannSphere

/-- **`MorseToSHDPHypothesis basis_ω`** is **unconditional** on
`RiemannSphere` at every choice of `basis_ω`. At genus 0 on RS, SHDP
is unconditionally inhabited (`nonempty_smoothHomologyDataPackage_
RiemannSphere`), so the Morse hypothesis is auto-discharged. -/
theorem morseToSHDPHypothesis_RiemannSphere
    (basis_ω : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
      (HolomorphicOneForm RiemannSphere)) :
    MorseToSHDPHypothesis (X := RiemannSphere) basis_ω := by
  intro _ _ _
  exact nonempty_smoothHomologyDataPackage_RiemannSphere basis_ω

end RiemannSphere

/-! ## T_L unconditional discharge -/

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`MorseToSHDPHypothesis (basis_g_dz L)`** is **unconditional** on
the complex torus `T_L = ℂ ⧸ L`. At genus 1 on `T_L`, SHDP at the
canonical basis `basis_g_dz L` is unconditionally inhabited
(`nonempty_smoothHomologyDataPackage_complexTorus`), so the Morse
hypothesis is auto-discharged. -/
theorem morseToSHDPHypothesis_complexTorus :
    MorseToSHDPHypothesis (X := ℂ ⧸ L) (basis_g_dz L) := by
  intro _ _ _
  exact nonempty_smoothHomologyDataPackage_complexTorus L

end ComplexTorus

end JacobianChallenge

end
