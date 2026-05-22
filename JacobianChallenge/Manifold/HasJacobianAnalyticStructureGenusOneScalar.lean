/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentGenusOneScalar

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` at genus 1 from a single scalar identity

End-to-end composition: at `genus X = 1`, the universal class
`HasJacobianAnalyticStructure X` follows from:

* `SurfaceClassificationData X` (topological surface classification +
  smooth Hurewicz);
* a single scalar identity for the Petersson form
  `H(basis_ω i₀, basis_ω i₀) = (2 · Im(star pm[k₀,i₀] · pm[k₁,i₀]) : ℂ)`.

Composes `HasC3FullClassicalContent.of_genus_one_pettersonScalar` with
the in-tree global bridge
`instHasJacobianAnalyticStructure_of_HasC3FullClassicalContent`.

## What ships

* `HasJacobianAnalyticStructure.of_genus_one_pettersonScalar` —
  constructor at `genus X = 1` taking `(SCD, basis_ω, k₀, k₁, i₀,
  scalar identity)` → `HasJacobianAnalyticStructure X`.

## Significance

At genus 1 on any compact connected complex 1-manifold, the open
analytic content for `HasJacobianAnalyticStructure X` reduces to a
single scalar identity for the Petersson form (plus the topological
SCD atom).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` at `genus X = 1` from a single
scalar identity for the Petersson form.** End-to-end composition. -/
theorem HasJacobianAnalyticStructure.of_genus_one_pettersonScalar
    (h_g : JacobianChallenge.genus X = 1)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (k₀ k₁ : Fin (2 * JacobianChallenge.genus X))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_scalar :
      (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₀)
        = ((2 *
            (star (periodMatrix (PeriodPairingData.ofSmoothCycle X)
                    basis_ω scd.symplecticBasis.cycleGens k₀ i₀)
              * periodMatrix (PeriodPairingData.ofSmoothCycle X)
                  basis_ω scd.symplecticBasis.cycleGens k₁ i₀).im : ℝ) : ℂ)) :
    HasJacobianAnalyticStructure X :=
  letI : HasC3FullClassicalContent X :=
    HasC3FullClassicalContent.of_genus_one_pettersonScalar h_g scd basis_ω
      k₀ k₁ h_k₀ h_k₁ i₀ h_scalar
  inferInstance

end JacobianChallenge

end
