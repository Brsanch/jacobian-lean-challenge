/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticJacobianSympComplexTorusEquiv
import JacobianChallenge.Manifold.AbelJacobiInjectiveComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Bijectivity of `abelJacobiPoint` on T_L (point-level, unconditional)

`abelJacobiPoint : ℂ⧸L → AnalyticJacobianSymp` is bijective on T_L,
**unconditional** of Abel/Jacobi. Combines the prior unconditional
`AbelJacobiInjectiveSymp` discharge with surjectivity derived from the
iso `AnalyticJacobianSymp ≃+ T_L`.

This is the **point-level** Abel-Jacobi bijection on T_L. The
divisor-level version (`Pic⁰ T_L ≃+ T_L`) is conditional on Abel/Jacobi
(see `Pic0EquivComplexTorus.lean`).

## What this file ships

* `abelJacobiPoint_surjective_complexTorus`: surjectivity unconditional.
* `abelJacobiPoint_bijective_complexTorus`: bijectivity unconditional.
* `relAbelJacobi_complexTorus`: explicit formula for the relative AJ.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Point-level surjectivity (unconditional) -/

/-- **`abelJacobiPoint : ℂ⧸L → AnalyticJacobianSymp` is surjective**,
unconditional. Every `v : AnalyticJacobianSymp` corresponds to
`Q := iso v ∈ T_L`, and `abelJacobiPoint Q = v` (via the iso punchline). -/
theorem abelJacobiPoint_surjective_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    Function.Surjective
      ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint
        : ℂ ⧸ L → AnalyticJacobianSymp _ (basis_g_dz L) h) := by
  intro v
  refine ⟨analyticJacobianSympEquiv_complexTorus L h v, ?_⟩
  apply (analyticJacobianSympEquiv_complexTorus L h).injective
  rw [analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]

/-! ## Point-level bijectivity (unconditional) -/

/-- **`abelJacobiPoint` is a bijection on T_L**, unconditional. -/
theorem abelJacobiPoint_bijective_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L)) :
    Function.Bijective
      ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint
        : ℂ ⧸ L → AnalyticJacobianSymp _ (basis_g_dz L) h) := by
  refine ⟨?_, abelJacobiPoint_surjective_complexTorus L h⟩
  have h_pos : 0 < JacobianChallenge.genus (ℂ ⧸ L) := by
    rw [genus_eq_one L]; exact Nat.one_pos
  exact abelJacobiInjective_complexTorus L h h_pos

/-! ## Explicit relative-AJ formula on T_L -/

/-- **The relative Abel-Jacobi map on `T_L` equals `Q - P` under the
iso.** -/
theorem relAbelJacobi_complexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (P Q : ℂ ⧸ L) :
    analyticJacobianSympEquiv_complexTorus L h
        ((canonicalAbelJacobiInputSymp L h).relAbelJacobi P Q)
      = Q - P := by
  show analyticJacobianSympEquiv_complexTorus L h
      ((canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q
        - (canonicalAbelJacobiInputSymp L h).abelJacobiPoint P)
    = Q - P
  rw [map_sub, analyticJacobianSympEquiv_complexTorus_abelJacobiPoint,
    analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]

end ComplexTorus

end JacobianChallenge

end
