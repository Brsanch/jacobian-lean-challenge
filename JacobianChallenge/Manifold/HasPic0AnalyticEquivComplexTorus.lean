/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HasPic0AnalyticEquiv
import JacobianChallenge.Manifold.Pic0EquivComplexTorus
import JacobianChallenge.Manifold.AnalyticJacobianSympComplexTorusEquiv

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! # `HasPic0AnalyticEquiv (ℂ ⧸ L)` — Phase C (T_L instance)

Discharges `Pic0AnalyticEquivBundle (ℂ ⧸ L)` conditional on the two
T_L-specific classical hypotheses:

* `TLDivSumHypothesis L` — Abel's elliptic theorem (kernel of period
  integration = principal divisors on `T_L`).
* `TLAbelConverseHypothesis L` — Weierstrass-σ existence (surjectivity
  of Abel-Jacobi on `T_L`).

The AddEquiv composition:

  `Pic⁰ (ℂ ⧸ L) ≃+ ℂ ⧸ L`  via `pic0EquivComplexTorus`
                            (`Pic0EquivComplexTorus.lean` line 42).
  `ℂ ⧸ L ≃+ AnalyticJacobianSymp _ _ h`  via `(analyticJacobianSympEquiv_complexTorus L h).symm`
                                          (`AnalyticJacobianSympComplexTorusEquiv.lean` line 105).
  `AnalyticJacobianSymp _ _ canonical = CanonicalAnalyticJacobian (basis_g_dz L)`
                              definitionally, when `h` is the canonical
                              `PeriodLatticeSymplecticBundle` extracted
                              from `[HasSmoothHomologyDataPackage (basis_g_dz L)]`.

`HasSmoothHomologyDataPackage (X := ℂ ⧸ L) (basis_g_dz L)` is an
unconditional instance (`SmoothHomologyDataPackageClass.lean` line 100).

This is a smoke test, not a Basic.lean flip. Basic.lean's item 5 is
universally quantified.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **The Pic⁰ ↔ analytic-Jacobian bundle on `ℂ ⧸ L`, conditional on the
two T_L classical hypotheses.**

The equiv is `pic0EquivComplexTorus` (Pic⁰ ↔ ℂ⧸L) composed with the
symmetric `analyticJacobianSympEquiv_complexTorus` at the canonical
bundle (ℂ⧸L ↔ CanonicalAnalyticJacobian, definitional). -/
noncomputable def pic0AnalyticEquivBundleComplexTorus
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Pic0AnalyticEquivBundle (ℂ ⧸ L) :=
  let h : PeriodLatticeSymplecticBundle
      (PeriodPairingData.ofSmoothCycle (ℂ ⧸ L)) (basis_g_dz L) :=
    canonicalPeriodLatticeSymplecticBundle (X := ℂ ⧸ L) (basis_g_dz L)
  { basis_ω := basis_g_dz L
    shdp := inferInstance
    equiv :=
      (pic0EquivComplexTorus L h hTL hConverse).trans
        (analyticJacobianSympEquiv_complexTorus L h).symm }

/-- **Nonempty form** — Phase C's classical-hypothesis-conditional
existence of the bundle on `ℂ ⧸ L`. -/
theorem nonempty_pic0AnalyticEquivBundleComplexTorus
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    Nonempty (Pic0AnalyticEquivBundle (ℂ ⧸ L)) :=
  ⟨pic0AnalyticEquivBundleComplexTorus L hTL hConverse⟩

/-- **`HasPic0AnalyticEquiv (ℂ ⧸ L)` from the two T_L hypotheses.**
Constructor — not a `[instance]` because the two T_L hypotheses are
not currently typeclasses themselves. Users with `(hTL, hConverse)`
in hand can apply this to obtain a class witness. -/
theorem hasPic0AnalyticEquivComplexTorus
    (hTL : TLDivSumHypothesis L)
    (hConverse : TLAbelConverseHypothesis L) :
    HasPic0AnalyticEquiv (ℂ ⧸ L) :=
  ⟨nonempty_pic0AnalyticEquivBundleComplexTorus L hTL hConverse⟩

end ComplexTorus

end JacobianChallenge

end
