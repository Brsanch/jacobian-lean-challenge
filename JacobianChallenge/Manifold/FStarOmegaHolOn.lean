/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FStarOmegaHolContMDiffAt
import JacobianChallenge.Manifold.HolomorphicOneFormOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmegaHol` packaged as a `HolomorphicOneFormOn` on `regularValueSet`

Holomorphic-side analogue of `MeromorphicNonzero.fStarOmegaOn`
(`Manifold/FStarOmegaOn.lean`). For a non-constant
`f : MeromorphicNonzero X` and a holomorphic 1-form
`α : HolomorphicOneForm X`, the trace `f.fStarOmegaHol hnc α` is
`ContMDiffOn 𝓘(ℂ, ℂ) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω` on the open
set `f.regularValueSet`. This packages it as a
`HolomorphicOneFormOn RiemannSphere f.regularValueSet`.

The proof composes:

* `fStarOmegaHol_contMDiffAt` — pointwise `ContMDiffAt ω` at every
  regular value (previous chip).
* `ContMDiffAt.contMDiffWithinAt` (mathlib) — `ContMDiffAt` implies
  `ContMDiffWithinAt` for any set; combined with the
  `ContMDiffOn ↔ ∀ point, ContMDiffWithinAt` characterisation gives
  the on-set version.

**Significance.** This is the smoothness side of the
`HolomorphicTraceExtension` construction: a holomorphic 1-form
defined on the *open regular set* `f.regularValueSet` whose
realified components agree pointwise with the realified trace. The
remaining classical content for `HolomorphicTraceExtension X` is
*extension across critical values* — n-th-root cancellation +
Riemann removable singularity theorem on 1-forms on `ℙ¹`, giving a
global `HolomorphicOneForm RiemannSphere` whose restriction to
`f.regularValueSet` agrees with this on-set construction. The
realification compatibility comes from the on-set side being defined
as the sum of source-side ℂ-linear pullbacks (which realify to the
realified pullbacks, agreeing with `traceAt` on real components by
the same source-fibre sum structure).

No `sorry`, no `axiom`. -/

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`fStarOmegaHol` is `ContMDiffOn ω` on `regularValueSet`.** -/
theorem fStarOmegaHol_contMDiffOn
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X) :
    ContMDiffOn (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) v
        (f.fStarOmegaHol hnc α v))
      f.regularValueSet := by
  intro v hv_reg
  exact (f.fStarOmegaHol_contMDiffAt hnc α hv_reg).contMDiffWithinAt

/-- **`fStarOmegaHol` packaged as a `HolomorphicOneFormOn` on the regular set.** -/
def fStarOmegaHolOn
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X) :
    HolomorphicOneFormOn RiemannSphere f.regularValueSet where
  toFun := f.fStarOmegaHol hnc α
  contMDiffOn_section := f.fStarOmegaHol_contMDiffOn hnc α

@[simp] lemma fStarOmegaHolOn_toFun
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X) (v : RiemannSphere) :
    (f.fStarOmegaHolOn hnc α).toFun v = f.fStarOmegaHol hnc α v := rfl

end MeromorphicNonzero

end JacobianChallenge

end
