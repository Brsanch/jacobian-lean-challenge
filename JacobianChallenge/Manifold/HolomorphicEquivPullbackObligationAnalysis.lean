/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicEquivSubsingletonTransfer
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100

/-! # Analysis of the pullback-smoothness obligation in the Riemann-sphere case

zz295 reduces item 14 reverse (`Subsingleton (HolomorphicOneForm X)`
from `HolomorphicEquiv X RiemannSphere`) to the named obligation
`IsHolomorphicOneFormPullback_for_all e.symm`.

This file analyzes the structure of that obligation in the
Riemann-sphere case and shows it is **equivalent** to the pointwise
pullback being identically zero. Concretely:

  `IsHolomorphicOneFormPullback_for_all (e.symm)
     ↔ (∀ α : HolomorphicOneForm X, ∀ y : RiemannSphere,
          e.symm.pullbackPointwise α y = 0)`

Direction (→): if the pullback is realized by some `pα :
HolomorphicOneForm RS`, then `pα = 0` (subsingleton) and `eval pα = 0`,
so the pullback function is the zero function.

Direction (←): take `pα := 0`; its eval is the zero function, which by
assumption equals the pullback.

This characterization clarifies what the analytic obligation actually
asks: that the *specific algebraic expression*
`(α.eval ∘ e.symm).comp (mfderiv e.symm)` is identically zero on `RS`
for every `α`. Equivalently, given the chain-rule identity from zz295,
the obligation is equivalent to `α = 0` for all `α` — i.e., the
subsingleton conclusion itself.

## What this file delivers

* `pullback_obligation_iff_pullbackPointwise_zero` — the equivalence.
* `pullback_obligation_iff_subsingleton` — composing with zz295's
  argument: the obligation is equivalent to `Subsingleton
  (HolomorphicOneForm X)`.

The genuine analytic discharge — proving the obligation directly via
the smoothness of the pullback section — is the substantive work
left to a future cotangent-pullback chip. This file makes explicit
that the named obligation IS the desired conclusion, modulo the
analytic content showing the pullback IS a smooth section (which in
turn forces it to be zero by subsingleton on RS).

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **Equivalence in the Riemann-sphere case.** The pullback-smoothness
obligation is equivalent to the pullback function being identically
zero. -/
theorem pullback_obligation_iff_pullbackPointwise_zero
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    IsHolomorphicOneFormPullback_for_all e.symm
      ↔ ∀ (α : HolomorphicOneForm X)
          (y : JacobianChallenge.RiemannSphere),
            e.symm.pullbackPointwise α y = 0 := by
  refine ⟨fun h α y => ?_, fun h α => ?_⟩
  · -- Forward direction.
    obtain ⟨pα, hpα⟩ := h α
    have hpα_zero : pα = 0 :=
      Subsingleton.elim pα 0
    have h_eval : HolomorphicOneForm.eval pα y = 0 := by
      rw [hpα_zero, HolomorphicOneForm.eval_zero]
    rw [← hpα y]; exact h_eval
  · -- Reverse direction. Take pα := 0.
    refine ⟨0, fun y => ?_⟩
    rw [HolomorphicOneForm.eval_zero]
    exact (h α y).symm

/-- **The obligation is equivalent to the subsingleton conclusion.**
Composing zz295's argument with the previous equivalence: the obligation
is equivalent to `Subsingleton (HolomorphicOneForm X)`. -/
theorem pullback_obligation_iff_subsingleton
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    IsHolomorphicOneFormPullback_for_all e.symm
      ↔ Subsingleton (HolomorphicOneForm X) := by
  refine ⟨fun h => ?_, fun h α => ?_⟩
  · exact HolomorphicOneForm.subsingleton_of_holomorphicEquiv_RiemannSphere
      e h
  · -- Subsingleton on X means α = 0 for every α; the pullback then has
    -- pα := 0 satisfying the eval equation pointwise (both sides 0).
    refine ⟨0, fun y => ?_⟩
    rw [HolomorphicOneForm.eval_zero]
    -- Goal: 0 = e.symm.pullbackPointwise α y.
    have hα_zero : α = 0 := @Subsingleton.elim _ h α 0
    rw [hα_zero]
    rw [HolomorphicEquiv.pullbackPointwise_zero e.symm]
    rfl

/-- **Headline equivalence.** Either supply the analytic obligation (a
direct proof that the pullback section is smooth), or already know the
target is subsingleton — they are equivalent. -/
theorem subsingleton_iff_pullback_obligation
    (e : HolomorphicEquiv X JacobianChallenge.RiemannSphere) :
    Subsingleton (HolomorphicOneForm X)
      ↔ IsHolomorphicOneFormPullback_for_all e.symm :=
  (pullback_obligation_iff_subsingleton e).symm

end JacobianChallenge

end
