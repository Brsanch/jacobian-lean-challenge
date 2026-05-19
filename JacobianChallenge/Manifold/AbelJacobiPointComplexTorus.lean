/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AbelJacobiInputSympComplexTorus
import JacobianChallenge.Manifold.ComplexTorusAlphaPeriodValue

set_option linter.unusedSectionVars false

/-! # Explicit formula for `abelJacobiPoint` on the complex torus

For the canonical `AbelJacobiInputSymp` on `T_L = ℂ ⧸ L`
(`canonicalAbelJacobiInputSymp L h`) at the canonical basis
`basis_g_dz L`, we compute the Abel-Jacobi point map explicitly:

  `(canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q
    = QuotientAddGroup.mk (fun _ : Fin (genus (ℂ ⧸ L)) => Q.out)`

Combining `complexChainPeriod_single_α_dz` (period of dz along `α L Q`
is `Q.out`) with the observation that `basis_g_dz L _ = dz L`
(since `Fin (genus T_L)` reindexes from `Fin 1` and `basis_one_dz L
0 = dz L`).

This is the analytic centerpiece for transporting the four open
classical hypotheses (Abel, Jacobi, smoothness, injectivity) to
identities on `T_L` via the canonical isomorphism
`AnalyticJacobianSymp ≅ T_L`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **`basis_g_dz L j = dz L` for every `j : Fin (genus (ℂ ⧸ L))`.**
Because `Fin 1` is subsingleton (`basis_one_dz L _ = dz L`) and
`basis_g_dz L j = basis_one_dz L (finCongr (genus_eq_one L) j)`. -/
lemma basis_g_dz_const (j : Fin (JacobianChallenge.genus (ℂ ⧸ L))) :
    basis_g_dz L j = dz L := by
  rw [basis_g_dz_apply]
  -- Now: basis_one_dz L (finCongr (genus_eq_one L) j) = dz L.
  -- Fin 1 is subsingleton, so the index is `0`.
  have h : finCongr (genus_eq_one L) j = 0 := Subsingleton.elim _ _
  rw [h, basis_one_dz_apply]

/-- **The period vector of `single (α L Q)` against `basis_g_dz L` is
constant-`Q.out`.** -/
theorem complexChainPeriodVector_basis_g_dz_α (Q : ℂ ⧸ L) :
    complexChainPeriodVector (basis_g_dz L) (SmoothChain.single (α L Q))
      = fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q.out := by
  funext j
  show complexChainPeriod (SmoothChain.single (α L Q)) (basis_g_dz L j) = Q.out
  rw [basis_g_dz_const]
  exact complexChainPeriod_single_α_dz L Q

/-- **Explicit Abel-Jacobi point map on `T_L`.**
`(canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q
  = QuotientAddGroup.mk (fun _ => Q.out)`. -/
theorem canonicalAbelJacobiInputSymp_abelJacobiPoint
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (Q : ℂ ⧸ L) :
    (canonicalAbelJacobiInputSymp L h).abelJacobiPoint Q
      = (QuotientAddGroup.mk (fun _ : Fin (JacobianChallenge.genus (ℂ ⧸ L)) => Q.out)
          : AnalyticJacobianSymp (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L))
              (basis_g_dz L) h) := by
  -- Unfold abelJacobiPoint to QuotientAddGroup.mk (complexChainPeriodVector ...).
  show abelJacobiPathSymp (basis_g_dz L) h
      ((canonicalAbelJacobiInputSymp L h).pathFromBase Q) = _
  unfold abelJacobiPathSymp
  -- pathFromBase Q = α L Q.
  show (QuotientAddGroup.mk (complexChainPeriodVector (basis_g_dz L)
          (SmoothChain.single (α L Q))) :
        AnalyticJacobianSymp _ _ _)
      = _
  rw [complexChainPeriodVector_basis_g_dz_α]

end ComplexTorus

end JacobianChallenge

end
