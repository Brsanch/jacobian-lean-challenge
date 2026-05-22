/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothChainPushIntegrate
import JacobianChallenge.Manifold.ComplexPeriodPairing
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackGeneral
import JacobianChallenge.Manifold.HolCotangentPullbackRealification
import JacobianChallenge.Manifold.ComplexToRealOmega

set_option linter.unusedSectionVars false

/-! # `complexPeriod` adjunction discharged unconditionally (chip 54)

The genuine analytic content of F8 OneForm functoriality:

  `complexPeriod (SmoothCycle.pushHom f hf_real_omega c) τ
    = complexPeriod c (HolomorphicOneForm.pullback f hf τ)`

for any holomorphic curve map `f : X → Y` and holomorphic 1-form
`τ : HolomorphicOneForm Y`. Where:

* `hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f` (complex-side holomorphicity).
* `hf_real_omega := ContMDiff.complex_to_real_omega hf` (real-side ω,
  via chip 54a).

This **discharges unconditionally** the `adjunction` hypothesis of
`PeriodPairingMorphism.ofSmoothCycle`, the last named analytic input
gating `canonicalPushforward_contMDiff` (item 18 of `Basic.lean`).

## Proof strategy

Decompose `complexPeriod` into real/imag parts:

  `complexPeriod c τ = (∫_c Re τ : ℂ) + i · (∫_c Im τ : ℂ)`.

Apply chip 53 (`SmoothCycle.integrate_pushHom`) to both summands:

  `∫_{push c} Re τ = ∫_c (SmoothOneForm.pullback f hf_real_omega (Re τ))`.

Identify `SmoothOneForm.pullback f hf_real_omega (realComponent τ)`
with `realComponent (HolomorphicOneForm.pullback f hf τ)` via
the realification compatibility theorem
`realPartCLM_holCotangentPullbackAt_apply` (sister
`HolCotangentPullbackRealification.lean`), ditto for `Im`. The
resulting RHS reassembles into `complexPeriod c (pullback τ)`.

## What this file ships

* `realComponent_HolomorphicPullback_eq_SmoothPullback` — compatibility
  identity for the real component.
* `imagComponent_HolomorphicPullback_eq_SmoothPullback` — same for
  imaginary.
* `complexPeriod_pushHom_eq_pullback` — the headline adjunction.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology Bundle ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ⊤ Y]

/-! ## Realification compatibility of pullback -/

/-- **Real component of the holomorphic pullback equals the
SmoothOneForm pullback of the real component.** Pointwise via
`realPartCLM_holCotangentPullbackAt_apply`. -/
theorem realComponent_HolomorphicPullback_eq_SmoothPullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (τ : HolomorphicOneForm Y) :
    realComponent (HolomorphicOneForm.pullback f hf τ)
      = SmoothOneForm.pullback (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
          f (ContMDiff.complex_to_real_omega hf) (realComponent τ) := by
  apply ContMDiffSection.ext
  intro x
  -- Pull out via ContinuousLinearMap.ext on the underlying `ℂ →L[ℝ] ℝ`.
  -- Both sides project to `ℂ →L[ℝ] ℝ` (definitional unfold of CotangentSpace).
  show (realComponent (HolomorphicOneForm.pullback f hf τ)).toFun x
      = (SmoothOneForm.pullback (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            f (ContMDiff.complex_to_real_omega hf) (realComponent τ)).toFun x
  -- Unfold realComponent on the LHS: this is just `(pullback τ).realPart x`.
  show (HolomorphicOneForm.pullback f hf τ).realPart x
      = (SmoothOneForm.pullback (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            f (ContMDiff.complex_to_real_omega hf) (realComponent τ)).toFun x
  -- Pointwise via CLM extensionality.
  apply ContinuousLinearMap.ext
  intro v
  have h_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x :=
    (hf x).mdifferentiableAt (by decide)
  -- LHS chain: realPart x v = realPartCLM ((pullback τ).eval x) v
  --                         = realPartCLM (holCotangentPullbackAt f x τ) v
  --                         = Re((τ.eval (f x)) (mfderiv_ℝ f x v))
  rw [show ((HolomorphicOneForm.pullback f hf τ).realPart x) v
        = (realPartCLM ((HolomorphicOneForm.pullback f hf τ).eval x)) v
      from by rw [realPartCLM_eval]]
  rw [show (HolomorphicOneForm.pullback f hf τ).eval x
        = holCotangentPullbackAt f x τ
      from rfl]
  rw [realPartCLM_holCotangentPullbackAt_apply h_mdiff τ v]
  -- RHS chain: (SmoothOneForm.pullback f hf_real_omega (realComponent τ)).toFun x v
  --       = ((realComponent τ (f x)).comp (mfderiv_ℝ f x)) v
  --       = (realComponent τ (f x)) (mfderiv_ℝ f x v)
  --       = (τ.realPart (f x)) (mfderiv_ℝ f x v)
  --       = Re((τ.eval (f x)) (mfderiv_ℝ f x v))
  show Complex.re ((τ.eval (f x))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v))
    = ((realComponent τ).toFun (f x)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v
  show Complex.re ((τ.eval (f x))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v))
    = (τ.realPart (f x)) ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v)
  rw [HolomorphicOneForm.realPart_apply]

/-- **Imaginary component of the holomorphic pullback equals the
SmoothOneForm pullback of the imaginary component.** -/
theorem imagComponent_HolomorphicPullback_eq_SmoothPullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (τ : HolomorphicOneForm Y) :
    imagComponent (HolomorphicOneForm.pullback f hf τ)
      = SmoothOneForm.pullback (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
          f (ContMDiff.complex_to_real_omega hf) (imagComponent τ) := by
  apply ContMDiffSection.ext
  intro x
  show (imagComponent (HolomorphicOneForm.pullback f hf τ)).toFun x
      = (SmoothOneForm.pullback (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            f (ContMDiff.complex_to_real_omega hf) (imagComponent τ)).toFun x
  show (HolomorphicOneForm.pullback f hf τ).imagPart x
      = (SmoothOneForm.pullback (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            f (ContMDiff.complex_to_real_omega hf) (imagComponent τ)).toFun x
  apply ContinuousLinearMap.ext
  intro v
  have h_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x :=
    (hf x).mdifferentiableAt (by decide)
  rw [show ((HolomorphicOneForm.pullback f hf τ).imagPart x) v
        = (imagPartCLM ((HolomorphicOneForm.pullback f hf τ).eval x)) v
      from by rw [imagPartCLM_eval]]
  rw [show (HolomorphicOneForm.pullback f hf τ).eval x
        = holCotangentPullbackAt f x τ
      from rfl]
  rw [imagPartCLM_holCotangentPullbackAt_apply h_mdiff τ v]
  show Complex.im ((τ.eval (f x))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v))
    = ((imagComponent τ).toFun (f x)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v
  show Complex.im ((τ.eval (f x))
        ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v))
    = (τ.imagPart (f x)) ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) v)
  rw [HolomorphicOneForm.imagPart_apply]

/-! ## Headline: complexPeriod adjunction discharged -/

/-- **The `complexPeriod` adjunction.** This is the genuine analytic
input to `PeriodPairingMorphism.ofSmoothCycle`, here discharged
unconditionally from chip 52 (path-level change of variables) + chip 53
(chain/cycle lift) + chip 54a (ω-level real realification) + the
realification compatibility lemmas. -/
theorem complexPeriod_pushHom_eq_pullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (c : SmoothCycle 𝓘(ℝ, ℂ) X) (τ : HolomorphicOneForm Y) :
    complexPeriod
        (SmoothCycle.pushHom f
          ((ContMDiff.complex_to_real_omega hf).of_le
            (le_top : (∞ : WithTop ℕ∞) ≤ ω)) c) τ
      = complexPeriod c (HolomorphicOneForm.pullback f hf τ) := by
  unfold complexPeriod
  -- Apply chip 53 to both real and imag integrate summands.
  rw [JacobianChallenge.SmoothCycle.integrate_pushHom
        (ContMDiff.complex_to_real_omega hf) c (realComponent τ)]
  rw [JacobianChallenge.SmoothCycle.integrate_pushHom
        (ContMDiff.complex_to_real_omega hf) c (imagComponent τ)]
  -- Identify SmoothOneForm.pullback (realComponent τ) with realComponent (pullback τ).
  rw [← realComponent_HolomorphicPullback_eq_SmoothPullback f hf τ,
      ← imagComponent_HolomorphicPullback_eq_SmoothPullback f hf τ]

end JacobianChallenge

end
