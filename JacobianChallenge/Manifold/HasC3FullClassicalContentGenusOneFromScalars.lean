/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasC3FullClassicalContent X` at genus 1 from SCD + single sesquilinear pairing

At `genus X = 1`, the g²-scalars discharge collapses to:
* `g(g − 1)/2 = 0` empty strict-upper Q vanishing;
* `g(g + 1)/2 = 1` upper-tri Petersson identity (single diagonal entry).

## What ships

* `HasC3FullClassicalContent.of_genus_one_pettersonPairing_scalars` —
  constructor at genus 1 from a SCD witness + a single sesquilinear
  pairing identity.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X` at `genus X = 1` from SCD + single
sesquilinear pairing identity, via the g²-scalars route.** -/
theorem HasC3FullClassicalContent.of_genus_one_pettersonPairing_scalars
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
    HasC3FullClassicalContent X := by
  haveI : Subsingleton (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; infer_instance
  apply HasC3FullClassicalContent.of_upperTriangularScalars scd basis_ω
  · intro i j hij
    have : i = j := Subsingleton.elim i j
    exact absurd this (ne_of_lt hij)
  · intro i j _hij
    have h_i : i = i₀ := Subsingleton.elim _ _
    have h_j : j = i₀ := Subsingleton.elim _ _
    rw [h_i, h_j]
    exact h_pair

end JacobianChallenge

end
