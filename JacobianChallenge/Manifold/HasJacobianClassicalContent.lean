/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureFromUpperTriangularScalars
import JacobianChallenge.Manifold.HasJacobianAnalyticStructureGenusZeroFromScalars
import JacobianChallenge.Manifold.SurfaceClassificationDataGenusZero
import JacobianChallenge.Manifold.DefaultHolomorphicOneFormBasis

set_option linter.unusedSectionVars false

/-! # `HasJacobianClassicalContent X` — typeclass bundling the g²-scalars route

A typeclass bundling the named classical content required to discharge
`HasJacobianAnalyticStructure X` via the g²-scalars route at general
genus:

* `SurfaceClassificationData X` (topology + smooth Hurewicz);
* a chosen ℂ-basis of `HolomorphicOneForm X`;
* `g(g − 1)/2` strict-upper Q vanishing identities (Stokes first-
  relation atom);
* `g(g + 1)/2` upper-tri Petersson sesquilinear pairing identities
  (Stokes / wedge / cup-product / second-relation atom).

The class provides a single named inhabitant for downstream consumers
that need only the **conclusion** `HasJacobianAnalyticStructure X` and
do not care about the specific basis or homology data.

## What ships

* `HasJacobianClassicalContent X` — class.
* `instance instHasJacobianAnalyticStructure_of_HasJacobianClassicalContent`
  — bridge instance.
* `instHasJacobianClassicalContent_RiemannSphere` — unconditional RS
  instance (genus 0, vacuous scalar families).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

/-- **`HasJacobianClassicalContent X`** — Prop class bundling the
named classical content for the C3 wave's analytic Jacobian structure
via the g²-scalars route at general genus. -/
class HasJacobianClassicalContent (X : Type u) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X] : Prop where
  /-- The witness: SCD + basis + g²-scalars. -/
  out :
    ∃ (scd : SurfaceClassificationData X)
        (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
          (HolomorphicOneForm X)),
      (∀ i j : Fin (JacobianChallenge.genus X), i < j →
        @riemannBilinearPeriodForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = 0) ∧
      (∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) *
          @periodSesquilinearForm X _ _ _
            (PeriodPairingData.ofSmoothCycle X)
            scd.symplecticBasis.cycleGens
            (standardSymplectic (JacobianChallenge.genus X))
            (basis_ω i) (basis_ω j)
          = (globalPettersonHermitianForm X).toFun (basis_ω i) (basis_ω j))

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Bridge from `[HasJacobianClassicalContent X]` to
`HasJacobianAnalyticStructure X`.** -/
instance instHasJacobianAnalyticStructure_of_HasJacobianClassicalContent
    [h : HasJacobianClassicalContent X] :
    HasJacobianAnalyticStructure X := by
  obtain ⟨scd, basis_ω, h_strict, h_upper⟩ := h.out
  exact HasJacobianAnalyticStructure.of_upperTriangularScalars scd basis_ω
    h_strict h_upper

namespace RiemannSphere

/-- **Unconditional RS instance.** At genus 0, both scalar families are
vacuous (empty Fin 0); the SCD discharges via
`surfaceClassificationData_RiemannSphere`. -/
instance instHasJacobianClassicalContent_RiemannSphere :
    HasJacobianClassicalContent RiemannSphere where
  out :=
    haveI : IsEmpty (Fin (JacobianChallenge.genus RiemannSphere)) := by
      rw [JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero]
      exact Fin.isEmpty
    ⟨surfaceClassificationData_RiemannSphere (Classical.arbitrary _),
     defaultHolomorphicOneFormBasis RiemannSphere,
     fun i _ _ => isEmptyElim i,
     fun i _ _ => isEmptyElim i⟩

end RiemannSphere

end JacobianChallenge

end
