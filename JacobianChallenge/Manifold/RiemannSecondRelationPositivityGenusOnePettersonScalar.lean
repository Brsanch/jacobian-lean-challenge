/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityFromBridge
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusOneScalar
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle

set_option linter.unusedSectionVars false

/-! # `RiemannSecondRelationPositivity` at genus 1 from a single scalar identity

At `genus X = 1`, the open input to `RiemannSecondRelationPositivity`
via the Petersson-form route reduces to a **single scalar identity**:

  `(globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₀)
   = (2 · Im(star (pm k₀ i₀) · pm k₁ i₀) : ℂ)`

where `pm := periodMatrix (PeriodPairingData.ofSmoothCycle X) basis_ω
cycleGens` and `k₀, k₁` are cycle indices with `.val = 0, 1`.

This composes:
* `hodgeRiemannBridgeHypothesis_of_genus_one_scalar` (scalar ⟹ matrix bridge);
* `riemannSecondRelationPositivity_of_bridge_pettersonForm` (matrix bridge +
  Petersson positive-definite ⟹ RSRP).

## What this file ships

* `riemannSecondRelationPositivity_of_genus_one_pettersonScalar` —
  composition: at `genus X = 1`, the scalar identity discharges
  `RiemannSecondRelationPositivity`.

## Significance

At genus 1, the open analytic input for the Petersson-form-based
discharge of the C3 wave's RSRP atom is now a single scalar identity —
the **fundamental Riemann area identity**:

  L²-norm of `ω₀` (Petersson diagonal) = 2 × Im(period product).

For general genus-1 `X`, this is the deep Stokes content that must be
checked once. On `T_L = ℂ ⧸ L` with explicit basis `{dz}` and periods
`(lam₁, lam₂)`, it is the area formula
`H(dz, dz) = 2 · Im(star lam₁ · lam₂)`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RiemannSecondRelationPositivity` at `genus X = 1` from the
genus-1 scalar bridge identity for the Petersson form.**

Composition of `hodgeRiemannBridgeHypothesis_of_genus_one_scalar`
(scalar ⟹ matrix bridge) and
`riemannSecondRelationPositivity_of_bridge_pettersonForm` (matrix
bridge + Petersson positive-definite ⟹ RSRP). -/
theorem riemannSecondRelationPositivity_of_genus_one_pettersonScalar
    (h_g : JacobianChallenge.genus X = 1)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X)
      → (PeriodPairingData.ofSmoothCycle X).H1)
    (k₀ k₁ : Fin (2 * JacobianChallenge.genus X))
    (h_k₀ : k₀.val = 0) (h_k₁ : k₁.val = 1)
    (i₀ : Fin (JacobianChallenge.genus X))
    (h_scalar :
      (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₀)
        = ((2 *
            (star (periodMatrix (PeriodPairingData.ofSmoothCycle X)
                    basis_ω cycleGens k₀ i₀)
              * periodMatrix (PeriodPairingData.ofSmoothCycle X)
                  basis_ω cycleGens k₁ i₀).im : ℝ) : ℂ)) :
    RiemannSecondRelationPositivity
      (PeriodPairingData.ofSmoothCycle X) basis_ω cycleGens := by
  have h_bridge :
      HodgeRiemannBridgeHypothesis (PeriodPairingData.ofSmoothCycle X)
        basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (globalPettersonHermitianForm X) :=
    hodgeRiemannBridgeHypothesis_of_genus_one_scalar h_g
      (PeriodPairingData.ofSmoothCycle X) basis_ω cycleGens
      (globalPettersonHermitianForm X) k₀ k₁ h_k₀ h_k₁ i₀ h_scalar
  exact riemannSecondRelationPositivity_of_bridge_pettersonForm
    (PeriodPairingData.ofSmoothCycle X) basis_ω cycleGens h_bridge

end JacobianChallenge

end
