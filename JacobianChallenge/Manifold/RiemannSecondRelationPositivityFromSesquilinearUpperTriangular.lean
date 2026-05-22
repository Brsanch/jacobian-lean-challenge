/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSecondRelationPositivityFromBridge
import JacobianChallenge.Manifold.HodgeRiemannBridgeSesquilinearUpperTriangular
import JacobianChallenge.Manifold.PeriodPairingDataFromSmoothCycle

set_option linter.unusedSectionVars false

/-! # `RiemannSecondRelationPositivity` from upper-triangular pairing identities

End-to-end composition at general genus:

  `g(g+1)/2` scalar pairing identities (Q_sq vs Petersson form on
  basis-pair upper triangle) ⟹ `RiemannSecondRelationPositivity`.

Composes:
* `hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular`
  (scalar pairing identities ⟹ bridge identity, chip 10);
* `riemannSecondRelationPositivity_of_bridge_pettersonForm`
  (bridge identity + Petersson PD ⟹ RSRP, chip 1).

## What ships

* `riemannSecondRelationPositivity_of_pettersonForm_sesquilinearUpperTriangular`
  — RSRP from `g(g+1)/2` upper-triangular Petersson scalar pairing
  identities, at any genus.

## Significance

The C3 wave's `RSRP` named atom at general genus reduces to a finite
family of `g(g+1)/2` scalar pairing identities, each of the form

  `I · Q_sq cycleGens (standardSymplectic g) (basis_ω i) (basis_ω j)
   = (globalPettersonHermitianForm X)(basis_ω i, basis_ω j)`

for `i ≤ j`. The Petersson form's positive-definiteness is
unconditional this session, so this is the cleanest expression of the
deep open analytic content at general genus.

At genus 0: `g(g+1)/2 = 0` identities (vacuous, recovers
unconditional discharge).
At genus 1: `1` scalar identity (matches the chip 4 fundamental
Riemann area identity).
At genus 2: `3` scalar identities (2 diagonal + 1 off-diagonal).
At genus g: `g(g+1)/2` scalar identities.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **RSRP at general genus from upper-triangular Petersson-pairing
identities.** -/
theorem riemannSecondRelationPositivity_of_pettersonForm_sesquilinearUpperTriangular
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X)
      → (PeriodPairingData.ofSmoothCycle X).H1)
    (h_upper :
      ∀ i j : Fin (JacobianChallenge.genus X), i.val ≤ j.val →
        (Complex.I : ℂ) * periodSesquilinearForm cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i) (basis_ω j)
          = (globalPettersonHermitianForm X).toFun (basis_ω i) (basis_ω j)) :
    RiemannSecondRelationPositivity
      (PeriodPairingData.ofSmoothCycle X) basis_ω cycleGens := by
  have h_bridge :
      HodgeRiemannBridgeHypothesis (PeriodPairingData.ofSmoothCycle X)
        basis_ω cycleGens
        (standardSymplectic (JacobianChallenge.genus X))
        (globalPettersonHermitianForm X) :=
    hodgeRiemannBridgeHypothesis_of_sesquilinearUpperTriangular
      (PeriodPairingData.ofSmoothCycle X) basis_ω cycleGens
      (globalPettersonHermitianForm X) h_upper
  exact riemannSecondRelationPositivity_of_bridge_pettersonForm
    (PeriodPairingData.ofSmoothCycle X) basis_ω cycleGens h_bridge

end JacobianChallenge

end
