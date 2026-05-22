/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasJacobianClassicalContent

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasJacobianClassicalContent X` at genus 2 from 4 explicit scalar identities

At `genus X = 2`, the g²-scalars discharge of HJCC reduces to:
* `g(g − 1)/2 = 1` strict-upper Q vanishing identity at `(i = 0, j = 1)`;
* `g(g + 1)/2 = 3` upper-tri Petersson sesquilinear identities at
  `(0, 0)`, `(0, 1)`, `(1, 1)`.

Total: **4 explicit scalar identities** + SCD.

## What ships

* `HasJacobianClassicalContent.of_genus_two` — builder lemma at genus
  2 taking 4 explicit scalar identities + SCD + a basis with `Fin 2`
  reindex.

## Significance

Documents the genus-2 concrete shape of the universal C3 wave's
analytic content. The chip is **conditional** at general X (the 4
identities are deep open Stokes / wedge / cup-product content).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`HasJacobianClassicalContent X` at `genus X = 2` from 4 explicit
scalar identities.**

Inputs:
* `SurfaceClassificationData X`;
* a basis `basis_ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`;
* `i₀, i₁ : Fin (genus X)` with `i₀.val = 0`, `i₁.val = 1`;
* `h_Q01 : Q J cycleGens (basis_ω i₀) (basis_ω i₁) = 0` (strict-upper);
* three Petersson pairing identities at `(i₀, i₀)`, `(i₀, i₁)`,
  `(i₁, i₁)`.
-/
theorem HasJacobianClassicalContent.of_genus_two
    (h_g : JacobianChallenge.genus X = 2)
    (scd : SurfaceClassificationData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (i₀ i₁ : Fin (JacobianChallenge.genus X))
    (h_i₀ : i₀.val = 0) (h_i₁ : i₁.val = 1)
    (h_Q01 :
      @riemannBilinearPeriodForm X _ _ _
          (PeriodPairingData.ofSmoothCycle X)
          scd.symplecticBasis.cycleGens
          (standardSymplectic (JacobianChallenge.genus X))
          (basis_ω i₀) (basis_ω i₁)
        = 0)
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
    HasJacobianClassicalContent X := by
  -- At g = 2, every index has val 0 or 1; cases on those two.
  have h_card : Fintype.card (Fin (JacobianChallenge.genus X)) = 2 := by
    rw [h_g]; simp [Fintype.card_fin]
  refine ⟨⟨scd, basis_ω, ?_, ?_⟩⟩
  · -- Strict-upper Q vanishing: i < j on Fin 2.
    intro i j hij
    -- i.val < j.val < 2, so (i.val, j.val) = (0, 1).
    have hij_lt : i.val < j.val := hij
    have hj_lt : j.val < 2 := by have hj := j.isLt; omega
    have hi_val : i.val = 0 := by omega
    have hj_val : j.val = 1 := by omega
    -- So i = i₀, j = i₁ via Fin.ext.
    have h_i_eq : i = i₀ := Fin.ext (hi_val.trans h_i₀.symm)
    have h_j_eq : j = i₁ := Fin.ext (hj_val.trans h_i₁.symm)
    rw [h_i_eq, h_j_eq]
    exact h_Q01
  · -- Upper-tri Petersson pairings: i ≤ j on Fin 2, so 3 cases.
    intro i j hij
    have hi_lt : i.val < 2 := by
      have hi := i.isLt
      omega
    have hj_lt : j.val < 2 := by
      have hj := j.isLt
      omega
    -- i.val ∈ {0, 1}, j.val ∈ {0, 1}, i.val ≤ j.val.
    rcases (by omega : i.val = 0 ∨ i.val = 1) with hi_v | hi_v
    · rcases (by omega : j.val = 0 ∨ j.val = 1) with hj_v | hj_v
      · -- (0, 0)
        have h_i_eq : i = i₀ := Fin.ext (hi_v.trans h_i₀.symm)
        have h_j_eq : j = i₀ := Fin.ext (hj_v.trans h_i₀.symm)
        rw [h_i_eq, h_j_eq]; exact h_pair_00
      · -- (0, 1)
        have h_i_eq : i = i₀ := Fin.ext (hi_v.trans h_i₀.symm)
        have h_j_eq : j = i₁ := Fin.ext (hj_v.trans h_i₁.symm)
        rw [h_i_eq, h_j_eq]; exact h_pair_01
    · -- i.val = 1; j.val ≥ 1, j.val < 2 ⟹ j.val = 1.
      have hj_v : j.val = 1 := by omega
      have h_i_eq : i = i₁ := Fin.ext (hi_v.trans h_i₁.symm)
      have h_j_eq : j = i₁ := Fin.ext (hj_v.trans h_i₁.symm)
      rw [h_i_eq, h_j_eq]; exact h_pair_11

end JacobianChallenge

end
