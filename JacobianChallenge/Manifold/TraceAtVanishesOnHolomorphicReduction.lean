/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FStarOmegaOn
import JacobianChallenge.Manifold.RegularLevelSetLatticeClauseFromTraceVanishing
import JacobianChallenge.Manifold.HolomorphicOneFormRealComponentLinear
import JacobianChallenge.Manifold.RiemannSphereChartSCoeffOverlap

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Structural reduction of `TraceAtVanishesOnHolomorphic`

The named hypothesis `TraceAtVanishesOnHolomorphic X`
(`Manifold/RegularLevelSetLatticeClauseFromTraceVanishing.lean`) asserts
that for every non-constant `f`, every `α : HolomorphicOneForm X`, and
every regular value `v`, both `f.traceAt hnc hv (realComponent α)` and
`f.traceAt hnc hv (imagComponent α)` vanish.

This file ships the **structural reduction** to a single named hypothesis
about the existence of a holomorphic 1-form on `RiemannSphere` that
realises the trace `f_*α` on the regular set:

* `HolomorphicTraceExtension X` — for every non-constant `f` and every
  `α : HolomorphicOneForm X`, there exists
  `α' : HolomorphicOneForm RiemannSphere` whose realified components
  agree pointwise on `f.regularValueSet` with the realified trace of
  the components of `α`.

* `traceAtVanishesOnHolomorphic_of_extension` — given
  `HolomorphicTraceExtension X`, `TraceAtVanishesOnHolomorphic X` holds.

The discharge composes:

1. The provided `α'` is `0` by `Subsingleton (HolomorphicOneForm
   RiemannSphere)` (an unconditional instance in tree from
   `Manifold/RiemannSphereChartSCoeffOverlap.lean`).
2. Hence `realComponent α' = 0` and `imagComponent α' = 0` (linearity,
   `Manifold/HolomorphicOneFormRealComponentLinear.lean`).
3. Pointwise evaluation gives `0` on the regular set.
4. The pointwise-agreement hypothesis (provided by the extension) then
   transports `0` back to the trace.

**Why this is a meaningful reduction.** The remaining content to
discharge `HolomorphicTraceExtension X` is exactly the *n-th-root
cancellation + Riemann removable singularity at critical values* — the
classical construction of `f_*α` as a holomorphic 1-form on `ℙ¹`. This
is genuinely-new classical content not at the current mathlib pin
(`8e3c989...`); the reduction here isolates it as a single named
input. The complementary smoothness/holomorphicity data on the *open*
`regularValueSet` is already supplied unconditionally by
`fStarOmegaOn` (`Manifold/FStarOmegaOn.lean`).

No `sorry`, no `axiom`. -/

open Set Filter Module
open scoped Manifold ContDiff Topology

noncomputable section

namespace JacobianChallenge

variable (X : Type*)
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ⊤ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [PreconnectedSpace X] [Nonempty X]

/-- **Holomorphic trace extension hypothesis.** For every non-constant
meromorphic function `f : MeromorphicNonzero X` and every holomorphic
1-form `α : HolomorphicOneForm X`, there exists a holomorphic 1-form
`α' : HolomorphicOneForm RiemannSphere` whose realified components
agree pointwise with the realified trace on the regular set:

  `(realComponent α').toFun v = f.traceAt hnc hv (realComponent α)`
  `(imagComponent α').toFun v = f.traceAt hnc hv (imagComponent α)`

(for every regular `v ∈ f.regularValueSet`).

This is the **single classical input** required to discharge
`TraceAtVanishesOnHolomorphic X`. Constructing `α'` requires:

1. Smoothness of the trace on `regularValueSet` — supplied
   unconditionally by `fStarOmegaOn`
   (`Manifold/FStarOmegaOn.lean`).
2. **Holomorphic** extension across critical values — the n-th-root
   cancellation + Riemann removable singularity argument. NOT yet at
   the mathlib pin; constitutes the remaining classical input.

The agreement is stated for the *real and imaginary components* (real
1-forms in the `𝓘(ℝ, ℂ)`-realified bundle), matching the form of
`TraceAtVanishesOnHolomorphic`. -/
def HolomorphicTraceExtension : Prop :=
  ∀ (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X),
    ∃ α' : HolomorphicOneForm RiemannSphere,
      ∀ {v : RiemannSphere} (hv : v ∈ f.regularValueSet),
        (realComponent α').toFun v = f.traceAt hnc hv (realComponent α) ∧
        (imagComponent α').toFun v = f.traceAt hnc hv (imagComponent α)

variable {X}

/-- **Reduction.** Given `HolomorphicTraceExtension X`,
`TraceAtVanishesOnHolomorphic X` holds.

The discharge uses `Subsingleton (HolomorphicOneForm RiemannSphere)`
(unconditional, in tree) to force the witnessing `α'` to be `0`, then
pushes the equality through `realComponent`/`imagComponent`-linearity. -/
theorem traceAtVanishesOnHolomorphic_of_extension
    (h : HolomorphicTraceExtension X) :
    TraceAtVanishesOnHolomorphic X := by
  intro f hnc α v hv
  obtain ⟨α', h_agree⟩ := h f hnc α
  -- α' = 0 by subsingleton.
  have hα'_zero : α' = 0 := Subsingleton.elim α' 0
  -- Push through realComponent / imagComponent.
  have h_re_zero : (realComponent α').toFun v = 0 := by
    rw [hα'_zero, realComponent_zero]
    rfl
  have h_im_zero : (imagComponent α').toFun v = 0 := by
    rw [hα'_zero, imagComponent_zero]
    rfl
  obtain ⟨h_re_agree, h_im_agree⟩ := h_agree hv
  refine ⟨?_, ?_⟩
  · -- f.traceAt hnc hv (realComponent α) = (realComponent α').toFun v = 0.
    rw [← h_re_agree]; exact h_re_zero
  · rw [← h_im_agree]; exact h_im_zero

/-- **Companion form.** Reduction of `RegularLevelSetLatticeClause`
discharge to `HolomorphicTraceExtension X`. Composes
`traceAtVanishesOnHolomorphic_of_extension` with
`regularLevelSetLatticeClause_of_traceVanishing`. -/
theorem regularLevelSetLatticeClause_of_holomorphicTraceExtension
    [DecidableEq X]
    {α_basis : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X)}
    {h_bundle : PeriodLatticeDiscretenessBundle
      (PeriodPairingData.ofSmoothCycle X) α_basis}
    (h : HolomorphicTraceExtension X) :
    RegularLevelSetLatticeClause X α_basis h_bundle :=
  regularLevelSetLatticeClause_of_traceVanishing
    (traceAtVanishesOnHolomorphic_of_extension h)

end JacobianChallenge

end
