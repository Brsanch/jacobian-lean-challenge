/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContent

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` at genus 1 from a single sesquilinear identity

A builder lemma constructing a `HasJacobianClassicalContent X`
witness at `genus X = 1` from:

* `SurfaceClassificationData X`;
* a basis `basis_ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`;
* a single sesquilinear pairing identity (the fundamental Riemann
  area identity for the Petersson form at the unique basis index).

The strict-upper Q vanishing family is empty (g(g-1)/2 = 0 at g = 1).
The upper-tri Petersson family collapses to the single diagonal entry
at (i₀, i₀).

## What ships

* `HasJacobianClassicalContent.of_genus_one_pettersonPairing` —
  builder lemma producing `HasJacobianClassicalContent X` at genus 1.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianClassicalContent X` at `genus X = 1` from a single
sesquilinear pairing identity.** -/
theorem HasJacobianClassicalContent.of_genus_one_pettersonPairing
    (h_g : JacobianChallenge.genus X = 1)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_pair :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₀)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₀)) :
    HasJacobianClassicalContent X := by
  haveI : Subsingleton (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; infer_instance
  refine ⟨⟨scd, basis_ω, ?_, ?_⟩⟩
  · -- Strict-upper Q vanishing: vacuous via Subsingleton (i < j impossible).
    intro i j hij
    have : i = j := Subsingleton.elim i j
    exact absurd this (ne_of_lt hij)
  · -- Upper-tri Petersson pairing: collapse all to (i₀, i₀).
    intro i j _hij
    have h_i : i = i₀ := Subsingleton.elim _ _
    have h_j : j = i₀ := Subsingleton.elim _ _
    rw [h_i, h_j]
    exact h_pair

end JacobianChallenge

end
