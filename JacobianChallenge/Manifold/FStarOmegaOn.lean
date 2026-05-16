/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.FStarOmegaContMDiffAt
import JacobianChallenge.Manifold.SmoothOneFormOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmega` packaged as a `SmoothOneFormOn` on `regularValueSet`

For a non-constant `f : MeromorphicNonzero X` and a smooth real 1-form
`om : SmoothOneForm 𝓘(ℝ, ℂ) X`, the trace `f.fStarOmega hnc om` (which is
the pointwise sum-of-cotangent-pullbacks at regular values, junk
elsewhere) is `ContMDiffOn 𝓘(ℝ, ℂ) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤`
on the open set `f.regularValueSet`. This packages it as a
`SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere f.regularValueSet`.

The proof composes:

* `fStarOmega_contMDiffAt` (sub-chip B) — pointwise `ContMDiffAt` at
  every regular value.
* `ContMDiffAt.contMDiffWithinAt` (mathlib) — `ContMDiffAt` implies
  `ContMDiffWithinAt` for any set; combined with the
  `ContMDiffOn ↔ ∀ point, ContMDiffWithinAt` characterisation gives the
  on-set version.

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

/-- **`fStarOmega` is `ContMDiffOn ⊤` on `regularValueSet`.** -/
theorem fStarOmega_contMDiffOn
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm (𝓘(ℝ, ℂ)) X) :
    ContMDiffOn (𝓘(ℝ, ℂ)) ((𝓘(ℝ, ℂ)).prod 𝓘(ℝ, ℂ →L[ℝ] ℝ)) ⊤
      (fun v : RiemannSphere => Bundle.TotalSpace.mk' (ℂ →L[ℝ] ℝ) v
        (f.fStarOmega hnc om v))
      f.regularValueSet := by
  intro v hv_reg
  exact (f.fStarOmega_contMDiffAt hnc om hv_reg).contMDiffWithinAt

/-- **`fStarOmega` packaged as a `SmoothOneFormOn` on the regular set.** -/
def fStarOmegaOn
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm (𝓘(ℝ, ℂ)) X) :
    SmoothOneFormOn (𝓘(ℝ, ℂ)) RiemannSphere f.regularValueSet where
  toFun := f.fStarOmega hnc om
  contMDiffOn_section := f.fStarOmega_contMDiffOn hnc om

@[simp] lemma fStarOmegaOn_toFun
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm (𝓘(ℝ, ℂ)) X) (v : RiemannSphere) :
    (f.fStarOmegaOn hnc om).toFun v = f.fStarOmega hnc om v := rfl

end MeromorphicNonzero

end JacobianChallenge

end
