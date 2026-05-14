/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobiInversionGenusZero
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Abel-Jacobi `AddEquiv` on `RiemannSphere`

`genus RiemannSphere = 0` is unconditional
(`Manifold/RiemannSphereChartSCoeffOverlap.lean`,
`genus_RiemannSphere_eq_zero`). Combined with the genus-0 discharges
of `AbelHypothesis` (`Manifold/AbelHypothesisGenusZero.lean`) and
`JacobiInversion` (`Manifold/JacobiInversionGenusZero.lean`), this
file specialises the full Abel-Jacobi iso construction
`abelJacobiEquiv_of_genus_zero` to `X = RiemannSphere`.

The one remaining classical input for the RS specialisation is
`Subsingleton (Pic0 RiemannSphere)` — the genus-0 case of Abel's
converse, equivalently the classical fact `Pic⁰(ℙ¹) = 0`.
Discharging it unconditionally in-tree requires explicit
construction of meromorphic representatives for every degree-0
divisor on `RiemannSphere`, which is a separate sub-chip.

## What ships

* `abelJacobiEquiv_of_RiemannSphere` — from `Subsingleton (Pic0
  RiemannSphere)` and an `AbelJacobiInput`/discreteness bundle,
  build `Pic0 RiemannSphere ≃+ AnalyticJacobian` on `RS`. Uses
  `genus_RiemannSphere_eq_zero` to discharge the genus-0 hypothesis
  automatically.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Submodule Module

namespace JacobianChallenge

namespace AbelJacobiInput

variable {α : Basis (Fin (JacobianChallenge.genus RiemannSphere)) ℂ
          (HolomorphicOneForm RiemannSphere)}
  {h : PeriodLatticeDiscretenessBundle
    (PeriodPairingData.ofSmoothCycle RiemannSphere) α}

/-- **Abel-Jacobi isomorphism on the Riemann sphere.** Specialises
`abelJacobiEquiv_of_genus_zero` to `X = RiemannSphere` using
`genus_RiemannSphere_eq_zero`. The single remaining hypothesis is
`Subsingleton (Pic0 RiemannSphere)`.

The composed result lets downstream code state the Abel-Jacobi iso
on the Riemann sphere as conditional on a single classical fact
(`Pic⁰(ℙ¹) = 0`), no longer on `AbelHypothesis` or `JacobiInversion`
separately. -/
noncomputable def abelJacobiEquiv_of_RiemannSphere
    (B : AbelJacobiInput α h)
    (hPic0 : Subsingleton (Pic0 RiemannSphere)) :
    Pic0 RiemannSphere ≃+
      AnalyticJacobian
        (PeriodPairingData.ofSmoothCycle RiemannSphere) α h :=
  B.abelJacobiEquiv_of_genus_zero JacobianChallenge.RiemannSphere.genus_RiemannSphere_eq_zero hPic0

end AbelJacobiInput

end JacobianChallenge

end
