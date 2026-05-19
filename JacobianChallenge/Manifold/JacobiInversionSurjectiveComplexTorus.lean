/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticJacobianSympComplexTorusEquiv
import JacobianChallenge.Manifold.AbelHypothesisReductionComplexTorus
import JacobianChallenge.Divisor.Single

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Surjectivity of `abelJacobi : Pic⁰ T_L → AnalyticJacobianSymp`

Conditional on `AbelHypothesis`, the AJ map on `Pic⁰ T_L` is surjective.

**Proof structure.** Given `v : AnalyticJacobianSymp`:
1. Let `Q := analyticJacobianSympEquiv L h v` ∈ T_L.
2. Build `D := Div.single Q - Div.single 0 : Div T_L`. Degree 0.
3. Project to `Pic⁰ T_L` and compute `abelJacobi hAbel (mk D)
   = abelJacobiPoint Q - abelJacobiPoint 0 = abelJacobiPoint Q`
   (since `abelJacobiPoint 0 = 0` because `(0 : T_L).out ∈ L`).
4. Under the iso, this equals `Q = iso v`. By iso bijection, equals `v`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## `abelJacobiPoint 0 = 0` -/

/-- **The canonical AJ-point map sends the basepoint `0 : ℂ⧸L` to `0`
in `AnalyticJacobianSymp`.** Because `(0 : ℂ⧸L).out ∈ L`, so the
constant function `fun _ => (0:ℂ⧸L).out` is in `periodLatticeImage`. -/
theorem abelJacobiPoint_basepoint_zero
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    (canonicalAbelJacobiInputSymp L h).abelJacobiPoint (0 : ℂ ⧸ L) = 0 := by
  rw [canonicalAbelJacobiInputSymp_abelJacobiPoint]
  -- Need: mk (fun _ => (0 : ℂ⧸L).out) = 0 in AnalyticJacobianSymp.
  -- (0 : ℂ⧸L).out ∈ L because L.mkQ (0 : ℂ⧸L).out = (0 : ℂ⧸L) = 0.
  have h_out_in_L : ((0 : ℂ ⧸ L).out : ℂ) ∈ L := by
    have h_mk : (Quotient.mk'' ((0 : ℂ ⧸ L).out) : ℂ ⧸ L) = (0 : ℂ ⧸ L) :=
      Quotient.out_eq _
    have : (L.mkQ : ℂ → ℂ ⧸ L) ((0 : ℂ ⧸ L).out) = 0 := h_mk
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  -- Now apply QuotientAddGroup.eq_zero_iff (re-typed via show).
  show (QuotientAddGroup.mk
      (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => (0 : ℂ ⧸ L).out)
      : (Fin (JacobianChallenge.genus (ℂ ⧸ L)) → ℂ) ⧸
          (PeriodLatticeOfRankTwoG.ofSymplectic
            (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h).lattice)
    = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rw [PeriodLatticeOfRankTwoG.ofSymplectic_lattice]
  exact const_mem_periodLatticeImage_of_mem_L L _ h_out_in_L

/-! ## `abelJacobiDivHom (Div.single x) = abelJacobiPoint x` -/

/-- **`abelJacobiDivHom` of a singleton divisor equals the AJ-point
map.** -/
theorem abelJacobiDivHom_single
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (x : ℂ ⧸ L) :
    haveI : DecidableEq (ℂ ⧸ L) := Classical.decEq _
    (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom (Div.single x)
      = (canonicalAbelJacobiInputSymp L h).abelJacobiPoint x := by
  classical
  show (canonicalAbelJacobiInputSymp L h).abelJacobiDiv (Div.single x)
    = _
  unfold AbelJacobiInputSymp.abelJacobiDiv
  rw [Div.supportFinset_single]
  rw [Finset.sum_singleton]
  rw [Div.single_apply]
  rw [if_pos rfl]
  rw [one_zsmul]

/-! ## `abelJacobi hAbel (mk D) = v` for `D = single Q - single 0` -/

/-- **Given `AbelHypothesis`, the AJ map on Pic⁰ T_L is surjective.** -/
theorem jacobiInversion_surjective_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hAbel : AbelJacobiInputSymp.AbelHypothesis (canonicalAbelJacobiInputSymp L h)) :
    Function.Surjective
      ((canonicalAbelJacobiInputSymp L h).abelJacobi hAbel) := by
  classical
  intro v
  -- Recover the corresponding T_L point.
  let Q : ℂ ⧸ L := analyticJacobianSympEquiv_complexTorus L h v
  -- The Div0 element [Q] - [0].
  let D : Div (ℂ ⧸ L) := Div.single Q - Div.single (0 : ℂ ⧸ L)
  have hD_mem : D ∈ Div0 (ℂ ⧸ L) :=
    Div.single_sub_single_mem_Div0 (0 : ℂ ⧸ L) Q
  let D₀ : Div0 (ℂ ⧸ L) := ⟨D, hD_mem⟩
  -- Pick its Pic⁰ class.
  let c : Pic0 (ℂ ⧸ L) := QuotientAddGroup.mk D₀
  refine ⟨c, ?_⟩
  -- Compute abelJacobi hAbel c = abelJacobiDiv0Hom D₀
  --                          = abelJacobiDivHom (single Q) - abelJacobiDivHom (single 0)
  --                          = abelJacobiPoint Q - abelJacobiPoint 0
  --                          = abelJacobiPoint Q - 0
  --                          = abelJacobiPoint Q
  show (canonicalAbelJacobiInputSymp L h).abelJacobi hAbel c = v
  rw [AbelJacobiInputSymp.abelJacobi_mk_eq_abelJacobiDiv]
  -- abelJacobiDiv (D₀ : Div) = abelJacobiDivHom D
  show (canonicalAbelJacobiInputSymp L h).abelJacobiDiv D = v
  -- D = single Q - single 0.
  have hD : D = Div.single Q - Div.single (0 : ℂ ⧸ L) := rfl
  rw [hD]
  -- abelJacobiDiv (single Q - single 0)
  --   = abelJacobiDivHom (single Q - single 0)
  --   = abelJacobiDivHom (single Q) - abelJacobiDivHom (single 0)
  have h_sub :
      (canonicalAbelJacobiInputSymp L h).abelJacobiDiv
          (Div.single Q - Div.single (0 : ℂ ⧸ L))
        = (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom (Div.single Q)
          - (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom (Div.single (0 : ℂ ⧸ L)) := by
    show (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom
        (Div.single Q - Div.single (0 : ℂ ⧸ L)) = _
    rw [map_sub]
  rw [h_sub]
  rw [abelJacobiDivHom_single, abelJacobiDivHom_single,
    abelJacobiPoint_basepoint_zero, sub_zero]
  -- Goal: abelJacobiPoint Q = v.
  -- Apply iso: iso (abelJacobiPoint Q) = Q = iso v.
  apply (analyticJacobianSympEquiv_complexTorus L h).injective
  rw [analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]

end ComplexTorus

end JacobianChallenge

end
