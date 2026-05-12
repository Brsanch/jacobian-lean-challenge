/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereChartNHolomorphy
import JacobianChallenge.Manifold.RiemannSphereLiouvilleFromSouthChart
import JacobianChallenge.Manifold.RiemannSphereSubsingletonReduction
import JacobianChallenge.Manifold.RiemannSphereGenusFromVanishing

/-! # Conditional closure of R1 (`genus RiemannSphere = 0`)

This file closes R1 (the named open `genus_RiemannSphere_statement`
from `RiemannSphereGenus.lean`) **conditionally on** a single
analytic ingredient about the cotangent-bundle's chartS-frame
coefficient.

## What is honestly proven (no `sorry`, no `axiom`)

* `subsingleton_HolomorphicOneForm_of_southChart_witness` —
  `Subsingleton (HolomorphicOneForm RiemannSphere)` follows from the
  assumption that for **every** holomorphic 1-form `om`, there exists a
  function `g : ℂ → ℂ` that
    1. is `ContinuousAt 0`,
    2. agrees with `om.eval ∞ 1` at `w = 0`, and
    3. satisfies the **classical cotangent transition**
       `g w = -chartNCoeff om w⁻¹ / w^2` on `w ≠ 0`.
  The proof composes the **entire-on-ℂ** property of `chartNCoeff om`
  (`zz270 chartNCoeff_differentiable`) with `zz258`'s
  `f_eq_zero_of_southChart_continuous` and `g_eq_zero_of_southChart_continuous`
  to force the form's chart coefficients (and the value at `∞`) to
  vanish; then `zz261 subsingleton_of_eval_at_one_eq_zero` packages
  this as `Subsingleton`.

* `genus_RiemannSphere_eq_zero_of_southChart_witness` — the genus form
  of the same conclusion.

## What is left open

The named hypothesis `R1Witness X` (defined here) is exactly the
classical content the eventual `Subsingleton(HolomorphicOneForm RS)`
proof needs from the cotangent-bundle machinery: the chartS-frame
local coefficient of every holomorphic 1-form is continuous at
`w = 0` (no pole at `∞`), agrees with the form's value at `∞`, and
transforms by `-1/w²` across the chartN/chartS overlap. The unconditional
closure of R1 reduces to providing a single witness of `R1Witness RS`,
which lives in the still-to-be-written chart-coefficient extraction
chase.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff OnePoint

namespace JacobianChallenge

namespace RiemannSphere

/-- **Named analytic ingredient for R1.** For every holomorphic 1-form
on the Riemann sphere, the (still-implicit) chartS-frame coefficient is
continuous at `0`, agrees with the form's value at `∞`, and satisfies
the classical cotangent transition across the chartN/chartS overlap. -/
def R1Witness : Prop :=
  ∀ om : HolomorphicOneForm RiemannSphere,
    ∃ g : ℂ → ℂ,
      ContinuousAt g 0 ∧
      g 0 = (om.eval (OnePoint.infty : OnePoint ℂ)) (1 : ℂ) ∧
      ∀ w : ℂ, w ≠ 0 → g w = -chartNCoeff om w⁻¹ / w ^ 2

/-- **Conditional Subsingleton.** From the R1 witness, every holomorphic
1-form on the Riemann sphere is zero, hence the space is a
subsingleton. -/
theorem subsingleton_HolomorphicOneForm_of_southChart_witness
    (h : R1Witness) :
    Subsingleton (HolomorphicOneForm RiemannSphere) := by
  -- It suffices to show every om : HolomorphicOneForm RS has
  -- om.eval x 1 = 0 for all x.
  refine subsingleton_of_eval_at_one_eq_zero (fun om x => ?_)
  -- Extract the witness g for this om.
  obtain ⟨g, h_cont, h_g0, h_overlap⟩ := h om
  -- Set f := chartNCoeff om. f is Differentiable ℂ (zz270).
  have h_f_diff : Differentiable ℂ (chartNCoeff om) :=
    chartNCoeff_differentiable om
  -- Apply zz258 to conclude chartNCoeff om = 0 and g = 0.
  have h_f_zero : chartNCoeff om = 0 :=
    f_eq_zero_of_southChart_continuous h_f_diff h_overlap h_cont
  have h_g_zero : g = 0 :=
    g_eq_zero_of_southChart_continuous h_f_diff h_overlap h_cont
  -- Case split on x.
  induction x using OnePoint.rec with
  | infty =>
    -- om.eval ∞ 1 = g 0 = 0.
    have h_g_zero_at : g 0 = 0 := by rw [h_g_zero]; rfl
    rw [← h_g0]
    exact h_g_zero_at
  | coe z =>
    -- om.eval ((z:RS)) 1 = chartNCoeff om z = 0.
    have h_eq : om.eval ((z : ℂ) : RiemannSphere) (1 : ℂ) = chartNCoeff om z := by
      rw [chartNCoeff_apply]
    rw [h_eq, h_f_zero]
    rfl

/-- **Conditional `genus RS = 0`.** From the R1 witness, the geometric
genus of the Riemann sphere is `0`. -/
theorem genus_RiemannSphere_eq_zero_of_southChart_witness
    (h : R1Witness) :
    JacobianChallenge.genus RiemannSphere = 0 :=
  haveI := subsingleton_HolomorphicOneForm_of_southChart_witness h
  genus_RiemannSphere_of_subsingleton

/-- Packaged against the named open statement `genus_RiemannSphere_statement`
from `RiemannSphereGenus.lean`. -/
theorem genus_RiemannSphere_statement_of_southChart_witness
    (h : R1Witness) :
    RiemannSphere.genus_RiemannSphere_statement :=
  genus_RiemannSphere_eq_zero_of_southChart_witness h

end RiemannSphere

end JacobianChallenge
