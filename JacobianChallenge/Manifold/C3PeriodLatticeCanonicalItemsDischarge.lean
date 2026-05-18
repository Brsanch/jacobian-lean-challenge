/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.C3PeriodLatticeStokesCanonicalRiemannSphere

set_option linter.unusedSectionVars false

/-! # Items 11/5/12 canonical-bundle discharge on `RiemannSphere`

Composes the canonical-bundle chain through
`PeriodLatticeSymplecticBundle` → `PeriodLatticeOfRankTwoG.ofSymplectic`
→ `JacobianOfLattice.CompactSpaceHypothesis` / `ChartedSpaceHypothesis`
to ship single-entry-point discharges for items 11 (compact), 5
(charted), 12 (charted) on `AnalyticJacobianSymp` for the Riemann
sphere via the canonical Stokes bundle.

Conditional on `Subsingleton (StokesBoundaryInvariance.canonical
𝓘(ℝ, ℂ) RiemannSphere).H1` (the canonical-Stokes-quotient analogue
of `H₁(S²; ℤ) = 0`).

## What this file ships

* `compactSpaceHypothesis_RiemannSphere_canonical` — item 11 discharge.
* `chartedSpaceHypothesis_RiemannSphere_canonical` — items 5/12 discharge.

Both via the canonical-bundle chain. Downstream consumers of items
11/5/12 on `JacobianAnalyticSymp` for RS get a single hypothesis
boundary.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module Submodule

namespace JacobianChallenge

variable
  (basis : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
    (HolomorphicOneForm RiemannSphere))

/-- **Item 11 (compact space) canonical-bundle discharge on RS.** -/
theorem compactSpaceHypothesis_RiemannSphere_canonical
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ)
        RiemannSphere).H1] :
    let h_bundle := periodLatticeSymplecticBundle_RiemannSphere_canonical basis
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      h_bundle
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h_bundle
    JacobianOfLattice.CompactSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle RiemannSphere) basis h_bundle) :=
  PeriodLatticeOfRankTwoG.ofSymplectic_compactSpace _ _ _

/-- **Items 5 + 12 (charted space) canonical-bundle discharge on RS.** -/
noncomputable def chartedSpaceHypothesis_RiemannSphere_canonical
    [Subsingleton (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ)
        RiemannSphere).H1] :
    let h_bundle := periodLatticeSymplecticBundle_RiemannSphere_canonical basis
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_discreteTopology_of_bundle
      h_bundle
    haveI := PeriodLatticeSymplecticBundle.periodLatticeImage_isZLattice_of_bundle h_bundle
    JacobianOfLattice.ChartedSpaceHypothesis
      (PeriodLatticeOfRankTwoG.ofSymplectic
        (PeriodPairingData.ofSmoothCycle RiemannSphere) basis h_bundle) :=
  PeriodLatticeOfRankTwoG.ofSymplectic_chartedSpace _ _ _

end JacobianChallenge

end
