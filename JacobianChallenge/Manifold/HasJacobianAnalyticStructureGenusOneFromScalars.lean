/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` at genus 1 from SCD + single pairing identity

At `genus X = 1`, the strict-upper Q vanishing family is empty
(`g(g − 1)/2 = 0` for `g = 1`). The upper-triangular Petersson
identity family has one entry (the diagonal at `(i₀, i₀)`).

So `HasJacobianAnalyticStructure X` at `genus X = 1` follows from:
* `SurfaceClassificationData X` (topology atom);
* a single sesquilinear pairing identity at the unique basis index.

This is the alternative genus-1 packaging via the g²-scalar route
(parallel to the existing `HasJacobianAnalyticStructure.of_genus_one_pettersonScalar`
which takes the equivalent matrix-form scalar identity).

## What ships

* `HasJacobianAnalyticStructure.of_genus_one_pettersonPairing` —
  constructor at genus 1 taking `(SCD, basis_ω, i₀, single pairing
  identity)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` at `genus X = 1` from SCD + a
single sesquilinear pairing identity.** -/
theorem HasJacobianAnalyticStructure.of_genus_one_pettersonPairing
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
    HasJacobianAnalyticStructure X := by
  haveI : Subsingleton (Fin (JacobianChallenge.genus X)) := by
    rw [h_g]; infer_instance
  apply HasJacobianAnalyticStructure.of_upperTriangularScalars scd basis_ω
  · -- Strict-upper Q vanishing: empty at g = 1 (i < j impossible on Subsingleton).
    intro i j hij
    -- i < j but Subsingleton ⟹ i = j, contradiction.
    have : i = j := Subsingleton.elim i j
    exact absurd this (ne_of_lt hij)
  · -- Upper Petersson identities: collapse all to (i₀, i₀) via Subsingleton.
    intro i j _hij
    have h_i : i = i₀ := Subsingleton.elim _ _
    have h_j : j = i₀ := Subsingleton.elim _ _
    rw [h_i, h_j]
    exact h_pair

end JacobianChallenge

end
