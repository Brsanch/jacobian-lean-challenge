/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianHodgeChainFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasJacobianHodgeChain X` at genus 1 from SCD + single sesquilinear identity

At `genus X = 1`, the g²-scalars discharge of HJHC collapses to:
* `g(g − 1)/2 = 0` empty strict-upper Q vanishing;
* `g(g + 1)/2 = 1` upper-tri Petersson identity (the unique diagonal
  entry (i₀, i₀)).

## What ships

* `HasJacobianHodgeChain.of_genus_one_pettersonPairing` —
  constructor at genus 1 from a SCD witness and a single sesquilinear
  pairing identity.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianHodgeChain X` at `genus X = 1` from SCD + single
sesquilinear pairing identity.** -/
theorem HasJacobianHodgeChain.of_genus_one_pettersonPairing
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
    HasJacobianHodgeChain X := by
  haveI : Subsingleton (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; infer_instance
  apply HasJacobianHodgeChain.of_upperTriangularScalars scd basis_ω
  · -- Strict-upper Q vanishing: empty at g = 1.
    intro i j hij
    have : i = j := Subsingleton.elim i j
    exact absurd this (ne_of_lt hij)
  · -- Upper Petersson identities: collapse to (i₀, i₀) via Subsingleton.
    intro i j _hij
    have h_i : i = i₀ := Subsingleton.elim _ _
    have h_j : j = i₀ := Subsingleton.elim _ _
    rw [h_i, h_j]
    exact h_pair

end JacobianChallenge

end
