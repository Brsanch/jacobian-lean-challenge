/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MorseSmoothHurewicz
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass

set_option linter.unusedSectionVars false

/-! # `MorseToSHDPHypothesis` trivially discharged from a nonempty SHDP

`MorseToSHDPHypothesis basis_ω` says: any perfect Morse function on X
produces a `SmoothHomologyDataPackage basis_ω`. When SHDP is *already*
nonempty (e.g., on RS, T_L, or any X with `[HasSmoothHomologyDataPackage
basis_ω]` instance), the bridge is trivially dischargeable: ignore the
Morse function, produce the existing SHDP witness.

This decouples Phase D's Morse-to-SHDP bridge from any X where SHDP
is independently available, leaving only `MorsePerfectExistsHypothesis`
as Phase D's real open content.

## What this file ships

* `morseToSHDPHypothesis_of_nonempty` — given `Nonempty
  (SmoothHomologyDataPackage basis_ω)`, the bridge is trivially true.
* `morseToSHDPHypothesis_of_hasSHDP` — class-form: from
  `[HasSmoothHomologyDataPackage basis_ω]` instance.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge: nonempty SHDP ⇒ `MorseToSHDPHypothesis`.** Ignores the
Morse function input. -/
theorem morseToSHDPHypothesis_of_nonempty
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (h : Nonempty (SmoothHomologyDataPackage basis_ω)) :
    MorseToSHDPHypothesis (X := X) basis_ω := by
  intro _ _ _
  exact h

/-- **Class-form: `[HasSmoothHomologyDataPackage basis_ω]` implies
`MorseToSHDPHypothesis basis_ω`.** Useful for X with subsingleton ω
(RS, T_L, biholomorphic-to-RS) where SHDP is an in-tree instance. -/
theorem morseToSHDPHypothesis_of_hasSHDP
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    [HasSmoothHomologyDataPackage (X := X) basis_ω] :
    MorseToSHDPHypothesis (X := X) basis_ω :=
  morseToSHDPHypothesis_of_nonempty
    (nonempty_smoothHomologyDataPackage_of_class)

end JacobianChallenge

end
