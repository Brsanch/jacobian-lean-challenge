/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContentGenusTwo
import JacobianChallenge.Manifold.RiemannFirstBilinearRelationGenusTwoLiteral
import JacobianChallenge.Manifold.HodgeRiemannBridgeGenusTwoRealDiagonal
import JacobianChallenge.Manifold.PeriodSesquilinearForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # `HasJacobianClassicalContent X` at genus 2 from 4 explicit literal scalars

End-to-end constructor at `genus X = 2` taking **4 explicit literal
period-matrix scalar identities** (1 bilinear strict-upper Q + 3
sesquilinear Petersson identities) + SCD.

## What ships

* `HasJacobianClassicalContent.of_genus_two_literalScalars` —
  constructor.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **HJCC at `genus X = 2` from 4 explicit literal scalar identities + SCD.**

Inputs:
* `h_g : genus X = 2`;
* `scd : SurfaceClassificationData X`;
* `basis_ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`;
* explicit indices `i₀, i₁` and `k₀, k₁, k₂, k₃` characterized by their
  natural-number values;
* **scalar 1**: the bilinear Q vanishing at `(i₀, i₁)` (RBFR atom);
* **scalars 2, 3**: real-part diagonal identities (Petersson diagonal
  = period intersection form);
* **scalar 4**: complex off-diagonal pairing identity. -/
theorem HasJacobianClassicalContent.of_genus_two_literalScalars
    (h_g : JacobianChallenge.genus X = 2)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (i₀ i₁ : Fin (JacobianChallenge.genus X))
    (h_i₀ : i₀.val = 0) (h_i₁ : i₁.val = 1)
    (_k₀ _k₁ _k₂ _k₃ : Fin (2 * JacobianChallenge.genus X))
    (_h_k₀ : _k₀.val = 0) (_h_k₁ : _k₁.val = 1)
    (_h_k₂ : _k₂.val = 2) (_h_k₃ : _k₃.val = 3)
    -- RBFR scalar.
    (h_Q01 :
      @riemannBilinearPeriodForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₁) = 0)
    -- Petersson scalars (3): diagonal at i₀, diagonal at i₁, off-diag (i₀, i₁).
    (h_pair_00 :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₀)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₀))
    (h_pair_01 :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₁)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₀) (basis_ω i₁))
    (h_pair_11 :
      (Complex.I : ℂ) *
        @periodSesquilinearForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₁) (basis_ω i₁)
        = (globalPettersonHermitianForm X).toFun (basis_ω i₁) (basis_ω i₁)) :
    HasJacobianClassicalContent X :=
  HasJacobianClassicalContent.of_genus_two h_g scd basis_ω i₀ i₁ h_i₀ h_i₁
    h_Q01 h_pair_00 h_pair_01 h_pair_11

end JacobianChallenge

end
