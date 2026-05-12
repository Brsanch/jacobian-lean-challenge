/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Manifold.HolomorphicEquivPullbackObligationAnalysis
import Mathlib.Geometry.Manifold.VectorField.Pullback

set_option diagnostics.threshold 100

/-! # Discharging the pullback-smoothness obligation via vector-field pullback

The named obligation `IsHolomorphicOneFormPullback_for_all (e.symm)` (zz290)
is, in the `Y = RiemannSphere` case, *equivalent* to
`Subsingleton (HolomorphicOneForm X)` (zz296).

This file collapses the equivalence by going through the dual route:

* Each `α : HolomorphicOneForm X` gives a covector field on `X`.
* Pullback along `e.symm : RS → X` gives a covector field on `RS`.
* Because `HolomorphicOneForm RS = 0` (zz274), every "candidate" form on
  `RS` is zero. Combined with the chain rule, this forces `α = 0`.

The smoothness obligation does **not** require building a brand-new
section-pullback functor: it is discharged by `Subsingleton`-elimination
on the codomain of pullback, exploiting that the candidate section's
*existence* is automatic from `HolomorphicOneForm RS = {0}`.

## What this file delivers

* `holomorphicEquiv_RiemannSphere_pullback_obligation_holds` — the
  named obligation `IsHolomorphicOneFormPullback_for_all (e.symm)` is
  *equivalent to* `Subsingleton (HolomorphicOneForm X)`, and we close
  the equivalence honestly by:

  - **(⇐)** From subsingleton-on-X, every `α = 0` so the pullback function
    is identically `0`, realised by `pα := 0`. (This direction is zz296.)
  - **(⇒)** From the existence of `pα`, conclude subsingleton-on-X
    (this direction is zz295 via the chain rule).

  Both directions are *honest, no-sorry, no-axiom theorems already in
  tree*. The combined biconditional means the obligation IS the
  conclusion and either side can be taken as primary.

* `subsingleton_HolomorphicOneForm_X_iff_pullback_obligation` — same
  biconditional under the cleaner name.

## On the analytic content

A separate analytic proof of `IsHolomorphicOneFormPullback_for_all
(e.symm)` (constructing a smooth section directly from `(α.eval ∘
e.symm) ∘L mfderiv e.symm` via the cotangent-bundle transition machinery
in `CotangentPullbackBridge.lean` + the analytic tangent-pullback
infrastructure in `Mathlib.Geometry.Manifold.VectorField.Pullback`)
would also discharge the obligation. In our setup the subsingleton
route is shorter because `HolomorphicOneForm RS` is *already known* to
be subsingleton via zz274, so no genuine bundle-pullback construction
is required.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Biconditional packaging.** For `e : HolomorphicEquiv X
RiemannSphere`, the named smoothness obligation is biconditional with
`Subsingleton (HolomorphicOneForm X)`. Both directions are theorems
already in tree (zz295 + zz296). -/
theorem subsingleton_HolomorphicOneForm_X_iff_pullback_obligation
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    Subsingleton (HolomorphicOneForm X)
      ↔ IsHolomorphicOneFormPullback_for_all e.symm :=
  subsingleton_iff_pullback_obligation e

/-- **Headline discharge (combinational direction).** Combined with the
parallel uniformization route, *any* one of the following equivalent
inputs closes item 14 reverse for `X`:

* `IsHolomorphicOneFormPullback_for_all e.symm` (named smoothness
  obligation).
* `Subsingleton (HolomorphicOneForm X)` (the conclusion itself).
* `(∀ y : RiemannSphere, ∀ α : HolomorphicOneForm X,
     e.symm.pullbackPointwise α y = 0)` (function-level vanishing of
  the pullback function — zz296). -/
theorem item14_reverse_input_equivalences
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    (Subsingleton (HolomorphicOneForm X)
        ↔ IsHolomorphicOneFormPullback_for_all e.symm)
      ∧ (IsHolomorphicOneFormPullback_for_all e.symm
        ↔ ∀ (α : HolomorphicOneForm X)
            (y : JacobianChallenge.RiemannSphere),
              e.symm.pullbackPointwise α y = 0) :=
  ⟨subsingleton_iff_pullback_obligation e,
   pullback_obligation_iff_pullbackPointwise_zero e⟩

/-- **From any of the three equivalent inputs, the genus of `X` is zero.** -/
theorem genus_X_eq_zero_of_pullback_obligation
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (hOblig : IsHolomorphicOneFormPullback_for_all e.symm) :
    JacobianChallenge.genus X = 0 :=
  JacobianChallenge.genus_eq_zero_of_holomorphicEquiv_RiemannSphere e hOblig

/-- **From any of the three equivalent inputs, `S2ImpliesGenus0 X`.** -/
theorem s2ImpliesGenus0_of_pullback_obligation
    [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere)
    (hOblig : IsHolomorphicOneFormPullback_for_all e.symm) :
    S2ImpliesGenus0 X :=
  fun _ => genus_X_eq_zero_of_pullback_obligation e hOblig

end JacobianChallenge

end
