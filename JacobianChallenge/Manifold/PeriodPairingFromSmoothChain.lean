/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChain
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.SmoothOneForm
import JacobianChallenge.Manifold.PeriodPairingDefinition

/-! # A concrete `PeriodPairing` candidate from smooth chains (chip ZZ147)

This file lifts the chain-side pairing

  `(c, ω) ↦ SmoothChain.integrate c ω`

provided by `SmoothPathIntegral.lean` (chip ZZ139, real-valued) to a
`PeriodPairingDataCandidate`-style bilinear pairing with
`SmoothChain I X` standing in for `H₁(X; ℤ)`.

## Scope reduction

The Tier-2 bundle `PeriodPairingData X` in
`PeriodPairingDefinition.lean` requires a pairing landing in
`HolomorphicOneForm X →ₗ[ℂ] ℂ`, i.e. a *complex-linear* functional on
*holomorphic* 1-forms. The infrastructure needed to build that pairing
from a smooth chain on a complex Riemann surface is:

* a real–imaginary decomposition `HolomorphicOneForm X → SmoothOneForm I X`
  (twice, for the real and imaginary parts of the cotangent value), where
  `I` is a real ModelWithCorners obtained by realifying `𝓘(ℂ)`, and
* the ZZ139 path integral on each summand,
* assembled into the complex value `realPart + i · imaginaryPart`.

Neither (i) the realification of `𝓘(ℂ)` to a real model with corners
matched against the ZZ113 / ZZ132 / ZZ139 stack, nor (ii) the explicit
real–imaginary split of a `ContMDiffSection` of the holomorphic
cotangent bundle, is wired through the repo at the current pin. Per
the strict-reader rule (`OPEN.md`), we therefore deliver the
*real-side* candidate only and leave the holomorphic upgrade to a
follow-up chip.

What this file provides:

* `smoothChain_realOneForm_pairing : SmoothChain I X → SmoothOneForm I X → ℝ`
  — alias for `SmoothChain.integrate` with the explicit pairing-shape signature.
* Linearity in each argument:
  * `_zero_left`, `_add_left`,
  * `_zero_right`, `_smul_right`.
* `smoothChain_realOneForm_pairingHom`: the bundled additive-monoid
  hom in the chain, for downstream use as a `H1`-style functional.

The "bundle into `PeriodPairingData`" step requires the holomorphic
upgrade noted above; pointer left as a docstring on
`smoothChain_realOneForm_pairingHom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

set_option diagnostics.threshold 100

namespace JacobianChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

/-- The concrete real-valued pairing on the chain side: integrate a
smooth real 1-form along a smooth singular 1-chain. This is exactly
`SmoothChain.integrate` (ZZ139) re-exposed in `pairing`-shape so that
downstream `PeriodPairing`-style code has a stable name. -/
def smoothChain_realOneForm_pairing
    (c : SmoothChain I X) (oneForm : SmoothOneForm I X) : ℝ :=
  SmoothChain.integrate c oneForm

@[simp] theorem smoothChain_realOneForm_pairing_zero_left
    (oneForm : SmoothOneForm I X) :
    smoothChain_realOneForm_pairing (0 : SmoothChain I X) oneForm = 0 := by
  unfold smoothChain_realOneForm_pairing
  exact SmoothChain.integrate_zero oneForm

theorem smoothChain_realOneForm_pairing_add_left
    (c₁ c₂ : SmoothChain I X) (oneForm : SmoothOneForm I X) :
    smoothChain_realOneForm_pairing (c₁ + c₂) oneForm
      = smoothChain_realOneForm_pairing c₁ oneForm
        + smoothChain_realOneForm_pairing c₂ oneForm := by
  unfold smoothChain_realOneForm_pairing
  exact SmoothChain.integrate_add c₁ c₂ oneForm

@[simp] theorem smoothChain_realOneForm_pairing_zero_right
    (c : SmoothChain I X) :
    smoothChain_realOneForm_pairing c (0 : SmoothOneForm I X) = 0 := by
  classical
  unfold smoothChain_realOneForm_pairing SmoothChain.integrate SmoothChain.asFinsupp
  refine Finset.sum_eq_zero ?_
  intro γ _
  rw [SmoothPath.integrate_zero]
  ring

theorem smoothChain_realOneForm_pairing_smul_right
    (c : SmoothChain I X) (a : ℝ) (oneForm : SmoothOneForm I X) :
    smoothChain_realOneForm_pairing c (a • oneForm)
      = a * smoothChain_realOneForm_pairing c oneForm := by
  classical
  unfold smoothChain_realOneForm_pairing SmoothChain.integrate SmoothChain.asFinsupp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro γ _
  rw [SmoothPath.integrate_smul]
  ring

/-- The chain-side pairing as an `AddMonoidHom` in the chain
argument, with the 1-form held fixed.

Downstream chips that want to upgrade the chain-side pairing to an
`H₁(X; ℤ) →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` for the Tier-2
`PeriodPairingData X` bundle will need:

* a realification of `𝓘(ℂ)` to a real `ModelWithCorners ℝ ℂ ℂ`
  matching the typeclasses on `SmoothChain` / `SmoothOneForm`, and
* a real–imaginary decomposition of `HolomorphicOneForm X` into a pair
  of `SmoothOneForm I X`s (the real and imaginary parts of the
  cotangent value).

Both are infrastructure currently missing from the repo at the present
mathlib pin; this hom is the chain-side ingredient ready for that
upgrade. -/
def smoothChain_realOneForm_pairingHom (oneForm : SmoothOneForm I X) :
    SmoothChain I X →+ ℝ where
  toFun c := smoothChain_realOneForm_pairing c oneForm
  map_zero' := smoothChain_realOneForm_pairing_zero_left oneForm
  map_add' c₁ c₂ := smoothChain_realOneForm_pairing_add_left c₁ c₂ oneForm

@[simp] theorem smoothChain_realOneForm_pairingHom_apply
    (oneForm : SmoothOneForm I X) (c : SmoothChain I X) :
    smoothChain_realOneForm_pairingHom oneForm c
      = smoothChain_realOneForm_pairing c oneForm := rfl

end JacobianChallenge

end
