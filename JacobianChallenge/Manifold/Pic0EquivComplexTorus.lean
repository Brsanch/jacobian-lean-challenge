/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobiInversionInjectiveComplexTorus

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # `Pic⁰ T_L ≃+ T_L` — the classical Abel-Jacobi isomorphism

The classical Abel-Jacobi theorem on the complex torus identifies the
Picard group `Pic⁰ T_L` with `T_L` itself. Conditional on the two
named classical hypotheses (`TLDivSumHypothesis L` and
`TLAbelConverseHypothesis L`), we ship this AddEquiv:

  `Pic⁰ (ℂ⧸L) ≃+ ℂ⧸L`

constructed by composing:
* `abelJacobiEquiv` (Pic⁰ ≃+ AnalyticJacobianSymp, from JacobiInversion).
* `analyticJacobianSympEquiv_complexTorus` (AnalyticJacobianSymp ≃+ T_L).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The classical Abel-Jacobi isomorphism on the complex torus**:
`Pic⁰ (ℂ⧸L) ≃+ ℂ⧸L`. Conditional on `TLDivSumHypothesis L`
(Abel's elliptic theorem) and `TLAbelConverseHypothesis L`
(Weierstrass σ-function existence). -/
noncomputable def pic0EquivComplexTorus
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Pic0 (ℂ ⧸ L) ≃+ (ℂ ⧸ L) :=
  let hAbel := abelHypothesis_complexTorus_of_TLDivSum L h hTL
  let hJI :=
    jacobiInversion_complexTorus_of_TLDivSum_and_TLAbelConverse L h hTL hConverse
  ((canonicalAbelJacobiInputSymp L h).abelJacobiEquiv hAbel hJI).trans
    (analyticJacobianSympEquiv_complexTorus L h)

/-- **The image of `[Q] - [0]` under the Abel-Jacobi iso equals `Q`.**
The canonical Abel-Jacobi point map factors through this iso as the
identity on the support-weighted divisor sum. -/
theorem pic0EquivComplexTorus_single_sub_single
    (h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L))
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L)
    (Q : ℂ ⧸ L) :
    haveI : DecidableEq (ℂ ⧸ L) := Classical.decEq _
    pic0EquivComplexTorus L h hTL hConverse
        (QuotientAddGroup.mk
          (⟨Div.single Q - Div.single (0 : ℂ ⧸ L),
            Div.single_sub_single_mem_Div0 (0 : ℂ ⧸ L) Q⟩ : Div0 (ℂ ⧸ L)))
      = Q := by
  classical
  -- Unfold pic0EquivComplexTorus = abelJacobiEquiv.trans iso.
  unfold pic0EquivComplexTorus
  show analyticJacobianSympEquiv_complexTorus L h
      ((canonicalAbelJacobiInputSymp L h).abelJacobiEquiv _ _ _) = Q
  -- abelJacobiEquiv (mk D₀) = abelJacobi (mk D₀) = ... = abelJacobiPoint Q.
  rw [AbelJacobiInputSymp.abelJacobiEquiv_apply,
    AbelJacobiInputSymp.abelJacobi_mk_eq_abelJacobiDiv]
  -- abelJacobiDiv (single Q - single 0) = abelJacobiPoint Q (via prior chip).
  have h_sub :
      (canonicalAbelJacobiInputSymp L h).abelJacobiDiv
          (Div.single Q - Div.single (0 : ℂ ⧸ L))
        = (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom (Div.single Q)
          - (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom (Div.single (0 : ℂ ⧸ L)) := by
    show (canonicalAbelJacobiInputSymp L h).abelJacobiDivHom
        (Div.single Q - Div.single (0 : ℂ ⧸ L)) = _
    rw [map_sub]
  rw [h_sub, abelJacobiDivHom_single, abelJacobiDivHom_single,
    abelJacobiPoint_basepoint_zero, sub_zero,
    analyticJacobianSympEquiv_complexTorus_abelJacobiPoint]

end ComplexTorus

end JacobianChallenge

end
