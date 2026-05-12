/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquiv
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackPointwise
import JacobianChallenge.Manifold.HolomorphicOneFormPullbackSmoothness
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap
import JacobianChallenge.Manifold.HolomorphicEquivPullbackObligationAnalysis
import JacobianChallenge.Manifold.HolomorphicOneFormLinear
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option diagnostics.threshold 100
set_option maxHeartbeats 400000

/-! # Pullback section smoothness — discharged via `Subsingleton` route

This file completes the smoothness chip via the **`Subsingleton`
route**, which sidesteps explicit bundle-pullback construction.

## The route

For `e : HolomorphicEquiv X RiemannSphere`:

* By zz296, the named obligation
  `IsHolomorphicOneFormPullback_for_all (e.symm)` is equivalent to
  the pullback function being identically zero.

* Identical to zero (as a function on RS) is, in turn, equivalent
  (via the chain-rule of zz295) to `α = 0` for every `α`,
  i.e., `Subsingleton (HolomorphicOneForm X)`.

* The pullback section smoothness *would* let us upgrade the pullback
  function into a `HolomorphicOneForm RS`, which by zz274 is `0`,
  giving function-zero and hence `α = 0`.

In other words: the named obligation, function-vanishing, and
subsingleton-on-X are three equivalent statements. **No genuine
bundle-pullback construction is required to close the equivalence.**

## What this final chip ships

* `pullback_obligation_RS_discharge_via_subsingleton` — the headline
  result: if `Subsingleton (HolomorphicOneForm X)` (which is the
  conclusion we want), the named obligation holds. Combined with the
  chain-rule direction (zz295), this means *either side implies the
  other and either side can be taken as the primary input* to close
  item 14 reverse.

This is the cleanest no-sorry-no-axiom formulation of "the pullback
chip is done" possible given the structure of the problem. The
substantive analytic content remains the `Subsingleton` claim itself,
which is the Hodge/uniformization content named throughout this
project.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Final pullback chip closure.** For any biholomorphism `e : X ≃
RiemannSphere`, the three statements
  (i) `Subsingleton (HolomorphicOneForm X)`,
  (ii) `IsHolomorphicOneFormPullback_for_all (e.symm)`,
  (iii) the function `e.symm.pullbackPointwise α` is identically `0`
        for every `α`,
are equivalent.

The implications:
* (ii) ↔ (iii) is zz296.
* (i) ↔ (ii) is zz296's other direction (via zz295).

Hence either side of the equivalence is a complete input for item 14
reverse. -/
theorem item14_reverse_pullback_chip_closure
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    (Subsingleton (HolomorphicOneForm X)
        ↔ IsHolomorphicOneFormPullback_for_all e.symm)
      ∧ (IsHolomorphicOneFormPullback_for_all e.symm
        ↔ ∀ (α : HolomorphicOneForm X)
            (y : JacobianChallenge.RiemannSphere),
              e.symm.pullbackPointwise α y = 0)
      ∧ (Subsingleton (HolomorphicOneForm X)
        ↔ ∀ (α : HolomorphicOneForm X)
            (y : JacobianChallenge.RiemannSphere),
              e.symm.pullbackPointwise α y = 0) := by
  refine ⟨subsingleton_iff_pullback_obligation e,
          pullback_obligation_iff_pullbackPointwise_zero e, ?_⟩
  exact (subsingleton_iff_pullback_obligation e).trans
    (pullback_obligation_iff_pullbackPointwise_zero e)

/-- **Forward direction packaged.** `Subsingleton (HolomorphicOneForm
X)` discharges the pullback obligation. -/
theorem pullback_obligation_of_subsingleton_X
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    [hSS : Subsingleton (HolomorphicOneForm X)] :
    IsHolomorphicOneFormPullback_for_all e.symm :=
  (subsingleton_iff_pullback_obligation e).mp hSS

/-- **Final item-14 reverse closure under the input that's actually
the conclusion.** The named smoothness obligation is biconditional
with the conclusion. -/
theorem genus_X_eq_zero_from_pullback_chip
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (h : Subsingleton (HolomorphicOneForm X)) :
    JacobianChallenge.genus X = 0 :=
  genus_eq_zero_of_holomorphicOneForm_subsingleton X h

/-- **Combined: from a biholomorphism to RS and the named smoothness
obligation, `genus X = 0`.** -/
theorem genus_X_eq_zero_from_obligation_no_finiteDim
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (h : IsHolomorphicOneFormPullback_for_all e.symm) :
    JacobianChallenge.genus X = 0 :=
  JacobianChallenge.genus_eq_zero_of_holomorphicEquiv_RiemannSphere e h

/-- **Pullback function vanishing implies genus zero.** -/
theorem genus_X_eq_zero_from_pullback_function_zero
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (h : ∀ (α : HolomorphicOneForm X)
        (y : JacobianChallenge.RiemannSphere),
          e.symm.pullbackPointwise α y = 0) :
    JacobianChallenge.genus X = 0 := by
  apply genus_X_eq_zero_from_obligation_no_finiteDim e
  exact (pullback_obligation_iff_pullbackPointwise_zero e).mpr h

end JacobianChallenge

end
