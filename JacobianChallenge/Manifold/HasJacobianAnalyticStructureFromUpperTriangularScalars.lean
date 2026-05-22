/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromUpperTriangularScalars

set_option linter.unusedSectionVars false

/-! # `HasJacobianAnalyticStructure X` from `g²` scalar identities + SCD

The end-to-end constructor at general genus on any compact connected
complex 1-manifold. Composes:

* `HasC3FullClassicalContent.of_upperTriangularScalars` — the C3
  umbrella from `g²` scalar identities + SCD;
* in-tree global bridge `HasC3FullClassicalContent X ⟹
  HasJacobianAnalyticStructure X`.

This is the **single cleanest open-input statement** for the universal
analytic Jacobian structure class at general genus on every compact
connected complex 1-manifold:

* `SurfaceClassificationData X` (topological atom);
* `g(g − 1)/2` bilinear strict-upper Q vanishing identities (Stokes
  first-relation atom);
* `g(g + 1)/2` sesquilinear upper Petersson identities (Stokes second-
  relation atom).

## What ships

* `HasJacobianAnalyticStructure.of_upperTriangularScalars` —
  constructor at general genus.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianAnalyticStructure X` from `g²` scalar identities + SCD,
at any genus.** -/
theorem HasJacobianAnalyticStructure.of_upperTriangularScalars
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (h_strict_Q :
      ∀ i j : Fin (JacobianChallenge.genus X), i < j →
        @riemannBilinearPeriodForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = 0)
    (h_upper_Qsq :
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) *
          @periodSesquilinearForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = (globalPettersonHermitianForm X).toFun (basis_ω i) (basis_ω j)) :
    HasJacobianAnalyticStructure X :=
  letI : HasC3FullClassicalContent X :=
    HasC3FullClassicalContent.of_upperTriangularScalars scd basis_ω
      h_strict_Q h_upper_Qsq
  inferInstance

end JacobianChallenge

end
