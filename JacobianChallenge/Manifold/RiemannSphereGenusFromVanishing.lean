/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereSubsingletonReduction
import JacobianChallenge.Manifold.RiemannSphereGenus

/-! # `genus RiemannSphere = 0` from pointwise vanishing of `om.eval _ 1`

End-to-end chain from the pointwise analytic statement to the geometric-
genus output:

```
  (∀ om : HolomorphicOneForm RS, ∀ x : RS, om.eval x 1 = 0)
    ──── zz261 ────►  Subsingleton (HolomorphicOneForm RS)
    ──── existing ──►  genus RiemannSphere = 0
```

The forward direction discharges the named open statement
`RiemannSphere.genus_RiemannSphere_statement` (from
`RiemannSphereGenus.lean`) from an entirely-pointwise analytic hypothesis
about `RiemannSphere`-valued forms.

The chart-coefficient form is also provided.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace RiemannSphere

/-- **End-to-end reduction.** From the pointwise hypothesis that for every
holomorphic 1-form `om` on the Riemann sphere and every point `x : RS`,
`om.eval x 1 = 0`, we conclude that the geometric genus of the Riemann
sphere is `0`. -/
theorem genus_RiemannSphere_eq_zero_of_eval_at_one_zero
    (h : ∀ (om : HolomorphicOneForm RiemannSphere) (x : RiemannSphere),
      om.eval x 1 = 0) :
    JacobianChallenge.genus RiemannSphere = 0 :=
  haveI := subsingleton_of_eval_at_one_eq_zero h
  genus_RiemannSphere_of_subsingleton

/-- **Chart-coefficient form.** From the hypothesis that every form has
both chart coefficients identically zero, the geometric genus of the
Riemann sphere is `0`. -/
theorem genus_RiemannSphere_eq_zero_of_chartCoeff_zero
    (h : ∀ om : HolomorphicOneForm RiemannSphere,
      chartNCoeff om = 0 ∧ chartSCoeff om = 0) :
    JacobianChallenge.genus RiemannSphere = 0 :=
  haveI := subsingleton_of_chartCoeff_eq_zero h
  genus_RiemannSphere_of_subsingleton

/-- **End-to-end reduction packaged against the named open statement.** -/
theorem genus_RiemannSphere_statement_of_eval_at_one_zero
    (h : ∀ (om : HolomorphicOneForm RiemannSphere) (x : RiemannSphere),
      om.eval x 1 = 0) :
    RiemannSphere.genus_RiemannSphere_statement :=
  genus_RiemannSphere_eq_zero_of_eval_at_one_zero h

/-- Chart-coefficient form, packaged against the named open statement. -/
theorem genus_RiemannSphere_statement_of_chartCoeff_zero
    (h : ∀ om : HolomorphicOneForm RiemannSphere,
      chartNCoeff om = 0 ∧ chartSCoeff om = 0) :
    RiemannSphere.genus_RiemannSphere_statement :=
  genus_RiemannSphere_eq_zero_of_chartCoeff_zero h

end RiemannSphere

end JacobianChallenge

end
