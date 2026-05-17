/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeLinearQuotient

set_option linter.unusedSectionVars false

/-! # Functoriality of `quotientLinearMap`

For ℂ-linear cover maps `T : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ)` carrying a
ℤ-lattice `L` into `L'`, the induced quotient map
`quotientLinearMap L L' T hT : (Fin g₁ → ℂ) ⧸ L → (Fin g₂ → ℂ) ⧸ L'`
already provides smoothness (`quotientLinearMap_contMDiff`). This file
adds the **functoriality** witnesses: identity, composition, and zero.

These are the foundational identities behind the AnalyticJacobian-level
functoriality of pushforward and pullback. They feed sister chips that
specialise to `JacobianAnalyticPushforwardLift.toQuotientMap_id'`,
`_comp`, and `_const`.

Each proof is a one-liner once we unfold to `Submodule.mapQ` and apply
the matching mathlib identity (`mapQ_id`, `mapQ_comp`, `mapQ_zero`).
-/

open Submodule

namespace JacobianChallenge

variable {g₁ g₂ g₃ : ℕ}
variable (L : Submodule ℤ (Fin g₁ → ℂ))
  [DiscreteTopology L] [IsZLattice ℝ L]
variable (L' : Submodule ℤ (Fin g₂ → ℂ))
  [DiscreteTopology L'] [IsZLattice ℝ L']
variable (L'' : Submodule ℤ (Fin g₃ → ℂ))
  [DiscreteTopology L''] [IsZLattice ℝ L'']

/-- **Identity functoriality.** The quotient-linear map induced by the
identity ℂ-CLM on `Fin g₁ → ℂ` (with `L` matched against itself) is the
identity on `(Fin g₁ → ℂ) ⧸ L`. -/
@[simp] theorem quotientLinearMap_id :
    (quotientLinearMap L L (ContinuousLinearMap.id ℂ (Fin g₁ → ℂ))
        (fun _ hx => hx) :
      (Fin g₁ → ℂ) ⧸ L → (Fin g₁ → ℂ) ⧸ L) = id := by
  funext q
  obtain ⟨y, rfl⟩ := L.mkQ_surjective q
  show quotientLinearMap L L _ _ (Submodule.Quotient.mk y) =
    Submodule.Quotient.mk y
  -- Unfold `quotientLinearMap` to `L.mapQ L (id.restrictScalars ℤ) _`,
  -- apply `mapQ_apply`, then `ContinuousLinearMap.id_apply`.
  show L.mapQ L
      ((ContinuousLinearMap.id ℂ (Fin g₁ → ℂ)).toLinearMap.restrictScalars ℤ)
      _ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
  rw [Submodule.mapQ_apply]
  rfl

/-- **Zero functoriality.** The quotient-linear map induced by the zero
ℂ-CLM `0 : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ)` (trivially matching `L`
into `L'`) is the constant zero map on the quotients. -/
@[simp] theorem quotientLinearMap_zero :
    (quotientLinearMap L L'
        (0 : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
        (fun _ _ => Submodule.zero_mem _) :
      (Fin g₁ → ℂ) ⧸ L → (Fin g₂ → ℂ) ⧸ L') = fun _ => 0 := by
  funext q
  obtain ⟨y, rfl⟩ := L.mkQ_surjective q
  show quotientLinearMap L L' _ _ (Submodule.Quotient.mk y) = 0
  show L.mapQ L'
      ((0 : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ)).toLinearMap.restrictScalars ℤ)
      _ (Submodule.Quotient.mk y) = 0
  rw [Submodule.mapQ_apply]
  show Submodule.Quotient.mk (0 : Fin g₂ → ℂ) = 0
  rfl

/-- **Composition functoriality.** The quotient-linear map induced by the
composition `T₂.comp T₁` equals the composition of the individual quotient
maps. -/
theorem quotientLinearMap_comp
    (T₁ : (Fin g₁ → ℂ) →L[ℂ] (Fin g₂ → ℂ))
    (T₂ : (Fin g₂ → ℂ) →L[ℂ] (Fin g₃ → ℂ))
    (h₁ : ∀ x ∈ L, T₁ x ∈ L')
    (h₂ : ∀ x ∈ L', T₂ x ∈ L'') :
    (quotientLinearMap L L'' (T₂.comp T₁)
        (fun x hx => h₂ _ (h₁ x hx)) :
      (Fin g₁ → ℂ) ⧸ L → (Fin g₃ → ℂ) ⧸ L'')
      = quotientLinearMap L' L'' T₂ h₂ ∘ quotientLinearMap L L' T₁ h₁ := by
  funext q
  obtain ⟨y, rfl⟩ := L.mkQ_surjective q
  change quotientLinearMap L L'' _ _ (Submodule.Quotient.mk y) =
    quotientLinearMap L' L'' T₂ h₂
      (quotientLinearMap L L' T₁ h₁ (Submodule.Quotient.mk y))
  change L.mapQ L''
      ((T₂.comp T₁).toLinearMap.restrictScalars ℤ) _
        (Submodule.Quotient.mk y) =
    L'.mapQ L'' (T₂.toLinearMap.restrictScalars ℤ) h₂
      (L.mapQ L' (T₁.toLinearMap.restrictScalars ℤ) h₁
        (Submodule.Quotient.mk y))
  rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.mapQ_apply]
  rfl

end JacobianChallenge
