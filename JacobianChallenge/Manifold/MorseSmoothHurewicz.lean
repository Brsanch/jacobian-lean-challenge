/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MorseIndex
import JacobianChallenge.Manifold.SmoothHomologyDataPackage
import JacobianChallenge.Manifold.SmoothHomologyDataPackageClass

set_option linter.unusedSectionVars false

/-! # Morse-theoretic discharge of smooth Hurewicz (Phase D-3 bridge)

The named-hypothesis bridge from Morse theory to the SmoothHomology
DataPackage. The chain Phase D constructs (over several future chips):

  Perfect Morse function `f` on `X`        [Phase D's open content]
  ⇒ CW decomposition with `1 + 2g + 1` cells indexed by critical points
  ⇒ The `2g` saddles give 2g stable-manifold 1-cells
  ⇒ Symplectic basis of `H₁(X; ℤ)` via intersection form
  ⇒ `SmoothHomologyDataPackage basis_ω` for the canonical basis.

The classical theorem ("every compact smooth manifold admits a Morse
function, every Morse function gives a CW decomposition, every CW
decomposition of an oriented closed surface gives a symplectic basis")
is **multi-step classical content not in mathlib**. This file factors
the chain into a single named hypothesis whose discharge is the
remaining open content of Phase D.

## What this file ships

* `MorsePerfectExistsHypothesis X g` — exists a perfect Morse function
  at genus `g`. The Morse-existence half of Phase D's open content.
* `MorseToSHDPHypothesis basis_ω` — given any perfect Morse function,
  one can construct a `SmoothHomologyDataPackage basis_ω`. The
  CW-decomposition / symplectic-basis half.
* `Nonempty.smoothHomologyDataPackage_of_morse_hypotheses` — bridge:
  `MorsePerfectExistsHypothesis X g + MorseToSHDPHypothesis basis_ω ⇒
   Nonempty (SmoothHomologyDataPackage basis_ω)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Morse-existence half -/

/-- **Perfect Morse function existence on a genus-`g` surface.**
Asserts the existence of a smooth function whose critical points form
the perfect-Morse configuration (one min, `2g` saddles, one max).

Open content: every compact smooth oriented 2-manifold admits such a
function (classical Morse theory; not in mathlib at the pin). -/
def MorsePerfectExistsHypothesis (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℝ, ℂ) ⊤ X] (g : ℕ) : Prop :=
  ∃ f : X → ℝ, IsMorseFunction f ∧ IsPerfectMorseAtGenus f g

/-! ## CW/symplectic-basis half -/

/-- **From a perfect Morse function, one can build a
`SmoothHomologyDataPackage`.**

Open content: the perfect Morse function's `2g` saddle critical
points' stable manifolds, paired via the intersection form, form a
symplectic basis of `H₁(X; ℤ)` and satisfy smooth-Hurewicz. This is
the CW-decomposition + symplectic-basis-extraction half of Phase D.

The hypothesis is parameterised by `basis_ω` because the
`bilinear` field of `SmoothHomologyDataPackage` (ℝ-LI of the `2g`
period vectors against `basis_ω`) depends on the basis choice. -/
def MorseToSHDPHypothesis
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)) : Prop :=
  ∀ {f : X → ℝ}, IsMorseFunction f →
    IsPerfectMorseAtGenus f (JacobianChallenge.genus X) →
    Nonempty (SmoothHomologyDataPackage basis_ω)

/-! ## Bridge: Phase D ⇒ `SmoothHomologyDataPackage` -/

/-- **Bridge.** Combining `MorsePerfectExistsHypothesis X g` and
`MorseToSHDPHypothesis basis_ω` produces a
`Nonempty (SmoothHomologyDataPackage basis_ω)`.

If both hypotheses are discharged unconditionally (the goal of Phase D),
this gives `Nonempty (SmoothHomologyDataPackage basis_ω)` for any
compact connected complex 1-manifold X at any basis, hence
`HasSmoothHomologyDataPackage X basis_ω` as an unconditional instance
— which is the Phase-D contribution to closing item 5 of `Basic.lean`. -/
theorem nonempty_smoothHomologyDataPackage_of_morse_hypotheses
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (h_exists : MorsePerfectExistsHypothesis X (JacobianChallenge.genus X))
    (h_bridge : MorseToSHDPHypothesis basis_ω) :
    Nonempty (SmoothHomologyDataPackage basis_ω) := by
  obtain ⟨f, hf_morse, hf_perfect⟩ := h_exists
  exact h_bridge hf_morse hf_perfect

/-- **`HasSmoothHomologyDataPackage` from the two Morse hypotheses.**
The class-form of the bridge above. -/
theorem hasSmoothHomologyDataPackage_of_morse_hypotheses
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    (h_exists : MorsePerfectExistsHypothesis X (JacobianChallenge.genus X))
    (h_bridge : MorseToSHDPHypothesis basis_ω) :
    HasSmoothHomologyDataPackage basis_ω where
  out := nonempty_smoothHomologyDataPackage_of_morse_hypotheses h_exists h_bridge

end JacobianChallenge

end
