/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiPointBijectiveComplexTorus
import JacobianChallenge.Manifold.JacobiInversionSurjectiveComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `abelJacobiPoint` on T_L is an `AddEquiv`

On the complex torus T_L = ℂ⧸L, the point-level Abel-Jacobi map
`abelJacobiPoint : ℂ⧸L → AnalyticJacobianSymp` is **additive** (a
group hom), not just bijective. Reason: `(a + b).out ≡ a.out + b.out
(mod L)`, and the constant-function difference at `L` is in
`periodLatticeImage`. Hence the AJ class respects addition.

Combined with the prior unconditional bijection, this upgrades to a
full `AddEquiv` ℂ⧸L ≃+ AnalyticJacobianSymp.

Importantly: this AddEquiv is **unconditional** of Abel/Jacobi, since
it's defined at the point level (no divisors involved).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Additivity of `abelJacobiPoint` -/

/-- **`abelJacobiPoint` respects addition on T_L.**
`abelJacobiPoint (a + b) = abelJacobiPoint a + abelJacobiPoint b`. -/
theorem abelJacobiPoint_map_add
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (a b : ℂ ⧸ L) :
    (canonicalAbelJacobiInputSymp L h).abelJacobiPoint (a + b)
      = (canonicalAbelJacobiInputSymp L h).abelJacobiPoint a
        + (canonicalAbelJacobiInputSymp L h).abelJacobiPoint b := by
  -- Use the iso: both sides map to the same element of T_L.
  apply (analyticJacobianSympEquiv_complexTorus L h).injective
  rw [map_add, analyticJacobianSympEquiv_complexTorus_abelJacobiPoint,
    analyticJacobianSympEquiv_complexTorus_abelJacobiPoint,
    analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]

/-- **`abelJacobiPoint 0 = 0`** (re-export from
`JacobiInversionSurjectiveComplexTorus`). -/
theorem abelJacobiPoint_map_zero
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    (canonicalAbelJacobiInputSymp L h).abelJacobiPoint (0 : ℂ ⧸ L) = 0 :=
  abelJacobiPoint_basepoint_zero L h

/-! ## `abelJacobiPoint` as a group hom -/

/-- **`abelJacobiPoint` as an `AddMonoidHom`** ℂ⧸L →+ AnalyticJacobianSymp. -/
noncomputable def abelJacobiPointHom
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    ℂ ⧸ L →+ AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h where
  toFun := (canonicalAbelJacobiInputSymp L h).abelJacobiPoint
  map_zero' := abelJacobiPoint_map_zero L h
  map_add' := abelJacobiPoint_map_add L h

@[simp] lemma abelJacobiPointHom_apply
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) (Q : ℂ ⧸ L) :
    abelJacobiPointHom L h Q = (canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q :=
  rfl

/-! ## `abelJacobiPoint` as an `AddEquiv` -/

/-- **`abelJacobiPoint` as an `AddEquiv`** ℂ⧸L ≃+ AnalyticJacobianSymp.
Unconditional. -/
noncomputable def abelJacobiPointEquiv
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    (ℂ ⧸ L) ≃+ AnalyticJacobianSymp
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) h :=
  AddEquiv.ofBijective (abelJacobiPointHom L h)
    (abelJacobiPoint_bijective_complexTorus L h)

@[simp] lemma abelJacobiPointEquiv_apply
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) (Q : ℂ ⧸ L) :
    abelJacobiPointEquiv L h Q =
      (canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q :=
  rfl

/-- **`abelJacobiPointEquiv` is the inverse of
`analyticJacobianSympEquiv_complexTorus`.** -/
theorem abelJacobiPointEquiv_eq_symm
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    abelJacobiPointEquiv L h
      = (analyticJacobianSympEquiv_complexTorus L h).symm := by
  apply AddEquiv.toEquiv_injective
  ext Q
  -- analyticJacobianSympEquiv (abelJacobiPointEquiv Q) = Q.
  apply (analyticJacobianSympEquiv_complexTorus L h).injective
  show analyticJacobianSympEquiv_complexTorus L h
      ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q)
    = analyticJacobianSympEquiv_complexTorus L h
        ((analyticJacobianSympEquiv_complexTorus L h).symm Q)
  rw [AddEquiv.apply_symm_apply]
  exact analyticJacobianSympEquiv_complexTorus_abelJacobiPoint L h Q

end ComplexTorus

end JacobianChallenge

end
