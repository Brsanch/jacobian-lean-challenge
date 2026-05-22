/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasC3FullClassicalContentFromBridge
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusOneScalar
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationGenusOne
import JacobianChallenge.Topology.Item14FromSubsingletonHolomorphicOneForm

set_option linter.unusedSectionVars false

/-! # `HasC3FullClassicalContent X` at genus 1 from a single scalar identity

At `genus X = 1`, the C3 wave umbrella class
`HasC3FullClassicalContent X` reduces from three named atoms (SCD,
RBFR, RSRP) to **two**:

* `SurfaceClassificationData X` — topological surface classification
  + smooth Hurewicz (a SCD witness picks the basepoint, symplectic
  basis, and Hurewicz hypothesis);
* a **single scalar identity** for the Petersson form `H` on the unique
  basis form `ω₀`:

  `H(basis_ω i₀, basis_ω i₀) = (2 · Im(star pm[k₀,i₀] · pm[k₁,i₀]) : ℂ)`.

The RBFR atom is unconditional at genus 1 via
`riemannFirstBilinearRelation_of_genus_one_standardSymplectic` (which
needs only `FiniteDimensional ℂ (HolomorphicOneForm X)`, itself
unconditional via `DiskChartCover.holomorphicOneFormFiniteDim_holds`).

The RSRP atom is discharged via the bridge composition through the
scalar identity (`riemannSecondRelationPositivity_of_bridge_pettersonForm`
composed with `hodgeRiemannBridgeHypothesis_of_genus_one_scalar`).

## What ships

* `HasC3FullClassicalContent.of_genus_one_pettersonScalar` —
  constructor at `genus X = 1` taking `(SCD, basis_ω, k₀, k₁, i₀,
  scalar identity)` → `HasC3FullClassicalContent X`.

## Significance

At genus 1, the open analytic content for the universal
`HasJacobianAnalyticStructure X` via the C3 umbrella reduces to:

* `SurfaceClassificationData X` (topology — the SCD atom);
* the **fundamental Riemann area identity** at genus 1 for the
  Petersson form.

The second is a single scalar equation per choice of basis, and is the
deep Stokes content at genus 1.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasC3FullClassicalContent X` at `genus X = 1` from a single
scalar identity for the Petersson form.**

Drops the RBFR named atom via `riemannFirstBilinearRelation_of_genus_one`
(at g = 1, RBFR is automatic from `Jᵀ = -J` since
`HolomorphicOneForm X` is 1-dim ℂ). Drops the RSRP named atom via
the bridge route through the scalar identity. -/
theorem HasC3FullClassicalContent.of_genus_one_pettersonScalar
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
    HasC3FullClassicalContent X := by
  -- RBFR at g = 1: unconditional via `riemannFirstBilinearRelation_of_genus_one_standardSymplectic`.
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X)
  have h_first :=
    riemannFirstBilinearRelation_of_genus_one_standardSymplectic
      (X := X) (data := PeriodPairingData.ofSmoothCycle X) h_g
      scd.symplecticBasis.cycleGens
  -- Matrix bridge at g = 1 from scalar identity.
  have h_bridge :=
    hodgeRiemannBridgeHypothesis_of_genus_one_scalar h_g
      (PeriodPairingData.ofSmoothCycle X) basis_ω
      scd.symplecticBasis.cycleGens
      (globalPettersonHermitianForm X) k₀ k₁ h_k₀ h_k₁ i₀ h_scalar
  exact HasC3FullClassicalContent.of_bridge_pettersonForm scd basis_ω
    h_first h_bridge

end JacobianChallenge

end
