/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RiemannSphereCoefficientVanishing

/-! # Reductions of `Subsingleton (HolomorphicOneForm RiemannSphere)`

This file packages two clean reductions of the gating input for challenge
item 14 reverse direction:

1. `subsingleton_of_eval_at_one_eq_zero` — if every holomorphic 1-form on
   `RiemannSphere` evaluated at any point and applied to `1 : ℂ` is zero,
   then `Subsingleton (HolomorphicOneForm RiemannSphere)`.

2. `subsingleton_of_chartCoeff_eq_zero` — same conclusion from the weaker
   hypothesis that every form has both chart coefficients identically
   zero. Routes through `eq_zero_of_chartCoeff_vanishing`.

Both reductions transfer the open frontier from the bundle-theoretic
`Subsingleton` statement to a *pointwise* analytic statement about
complex-valued functions on `ℂ`, which can then be attacked via
`RiemannSphereLiouvilleFromSouthChart.f_eq_zero_of_southChart_continuous`
and the manifold-glue chart-coefficient extraction.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

namespace RiemannSphere

/-- **First reduction.** If for every holomorphic 1-form `om` on the
Riemann sphere and every point `x : RiemannSphere`, the cotangent vector
`om.eval x` vanishes on `1 : ℂ`, then `HolomorphicOneForm RiemannSphere`
is a subsingleton.

Proof: pointwise vanishing of `om.eval x 1` forces `om.eval x = 0`
(by `cotangent_eq_zero_of_apply_one_zero`), which forces `om = 0` (by
`eq_zero_iff_eval_eq_zero`). Then every form equals `0`, so the type is
subsingleton via `subsingleton_of_forall_eq`. -/
theorem subsingleton_of_eval_at_one_eq_zero
    (h : ∀ (om : HolomorphicOneForm RiemannSphere) (x : RiemannSphere),
      om.eval x 1 = 0) :
    Subsingleton (HolomorphicOneForm RiemannSphere) := by
  refine subsingleton_of_forall_eq 0 (fun om => ?_)
  rw [eq_zero_iff_eval_eq_zero]
  exact fun x => (eval_eq_zero_iff_apply_one_zero om x).mpr (h om x)

/-- **Second reduction.** If every holomorphic 1-form on the Riemann
sphere has both chart coefficients identically zero, then
`HolomorphicOneForm RiemannSphere` is a subsingleton.

Proof: each form is zero by `eq_zero_of_chartCoeff_vanishing`; apply
`subsingleton_of_forall_eq`. -/
theorem subsingleton_of_chartCoeff_eq_zero
    (h : ∀ om : HolomorphicOneForm RiemannSphere,
      chartNCoeff om = 0 ∧ chartSCoeff om = 0) :
    Subsingleton (HolomorphicOneForm RiemannSphere) := by
  refine subsingleton_of_forall_eq 0 (fun om => ?_)
  obtain ⟨hN, hS⟩ := h om
  exact eq_zero_of_chartCoeff_vanishing hN hS

/-! ### Iff-forms (no new content, packaging for reuse) -/

/-- A holomorphic 1-form on the Riemann sphere is zero iff its
cotangent value applied to `1 : ℂ` is zero at every point. -/
theorem eq_zero_iff_eval_at_one_eq_zero (om : HolomorphicOneForm RiemannSphere) :
    om = 0 ↔ ∀ x : RiemannSphere, om.eval x 1 = 0 := by
  rw [eq_zero_iff_eval_eq_zero]
  refine forall_congr' (fun x => ?_)
  exact eval_eq_zero_iff_apply_one_zero om x

/-- A holomorphic 1-form on the Riemann sphere is zero iff both its
chart coefficients vanish identically. -/
theorem eq_zero_iff_chartCoeff_eq_zero (om : HolomorphicOneForm RiemannSphere) :
    om = 0 ↔ chartNCoeff om = 0 ∧ chartSCoeff om = 0 := by
  refine ⟨fun h => ?_, fun ⟨hN, hS⟩ => eq_zero_of_chartCoeff_vanishing hN hS⟩
  rw [h]
  exact ⟨chartNCoeff_zero, chartSCoeff_zero⟩

end RiemannSphere

end JacobianChallenge

end
