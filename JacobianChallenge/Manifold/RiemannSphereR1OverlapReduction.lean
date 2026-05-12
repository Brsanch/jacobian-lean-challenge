/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffProper
import JacobianChallenge.Manifold.RiemannSphereR1ConditionalClose

/-! # Reduction of R1 to the cotangent overlap formula

Combining `zz272 chartSCoeffProper_continuousAt_zero` and
`chartSCoeffProper_zero` with `zz271`'s `R1Witness` shape, this file
reduces the unconditional closure of R1 to a **single** named
hypothesis: the cotangent-bundle transition formula
`chartSCoeffProper om w = -chartNCoeff om w⁻¹ / w^2` for `w ≠ 0`.

In other words, the unconditional R1 close = "discharge
`R1OverlapFormula`" below. That discharge is the explicit cotangent-
bundle transition computation under the chart transition `z ↦ z⁻¹`,
combining `cotangentBundleCore_coordChange_apply` with
`tangentBundleCore_coordChange_achart`, `fderiv_inv`, and the
extChartAt unfolding for `OnePoint ℂ`'s chartN / chartS.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- **Named open hypothesis (the only remaining input for R1).** For every
holomorphic 1-form on the Riemann sphere, the proper chartS-frame
coefficient satisfies the classical cotangent transition on the
chartN / chartS overlap `w ≠ 0`. -/
def R1OverlapFormula : Prop :=
  ∀ om : HolomorphicOneForm RiemannSphere, ∀ w : ℂ, w ≠ 0 →
    chartSCoeffProper om w = -chartNCoeff om w⁻¹ / w ^ 2

/-- **R1Witness from the overlap formula.** zz272's continuity at `0` and
zero-value identity for `chartSCoeffProper`, together with the named
overlap formula, produce a full `R1Witness`. -/
theorem R1Witness_of_overlapFormula (h : R1OverlapFormula) : R1Witness := by
  intro om
  refine ⟨chartSCoeffProper om,
    chartSCoeffProper_continuousAt_zero om,
    chartSCoeffProper_zero om,
    ?_⟩
  intro w hw
  exact h om w hw

/-- **Conditional Subsingleton** from the overlap formula. -/
theorem subsingleton_HolomorphicOneForm_of_overlapFormula
    (h : R1OverlapFormula) :
    Subsingleton (HolomorphicOneForm RiemannSphere) :=
  subsingleton_HolomorphicOneForm_of_southChart_witness
    (R1Witness_of_overlapFormula h)

/-- **Conditional `genus RS = 0`** from the overlap formula. -/
theorem genus_RiemannSphere_eq_zero_of_overlapFormula
    (h : R1OverlapFormula) :
    JacobianChallenge.genus RiemannSphere = 0 :=
  genus_RiemannSphere_eq_zero_of_southChart_witness
    (R1Witness_of_overlapFormula h)

/-- **Packaged against the named open statement** from
`RiemannSphereGenus.lean`. -/
theorem genus_RiemannSphere_statement_of_overlapFormula
    (h : R1OverlapFormula) :
    RiemannSphere.genus_RiemannSphere_statement :=
  genus_RiemannSphere_eq_zero_of_overlapFormula h

end RiemannSphere

end JacobianChallenge
