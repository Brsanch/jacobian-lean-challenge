/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmega`: trace as a `v`-varying section

For `f : MeromorphicNonzero X` non-constant and `om : SmoothOneForm 𝓘(ℝ, ℂ) X`,
the **pushforward 1-form** `f_*om` is canonically defined only at regular
values: at `v ∈ f.regularValueSet`, its value is the pointwise trace
`f.traceAt hnc hv om : CotangentSpace 𝓘(ℝ, ℂ) v`. Off the regular-value
set the pushforward 1-form has no canonical value (the fibre is no longer
a finite set of local-biholomorphism preimages).

This file packages the pointwise trace as a `v`-varying section
`fStarOmega f hnc om : (v : RiemannSphere) → CotangentSpace 𝓘(ℝ, ℂ) v`,
returning the trace at regular values and `0` at critical values (junk).
This is the dependent function form needed downstream to extract a
`SmoothOneFormOn 𝓘(ℝ, ℂ) RiemannSphere f.regularValueSet` (subsequent
chip `f-5`).

The `0` choice off the regular-value set is convenient — it gives a
total function so the downstream "smooth-on-regularValueSet" packaging
needs only local agreement. Smoothness on `regularValueSet` is the
content of subsequent chips; this file only provides the definition and
its action at regular values.

ℝ-linearity in the 1-form descends pointwise from
`MeromorphicNonzero.traceAt_{zero, add, smul}`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`f_*om` as a `v`-varying section.** At a regular value `v`,
returns `f.traceAt hnc hv om`. Off the regular-value set, returns `0`
(junk). Total dependent function so downstream smoothness packaging
only needs local agreement on `regularValueSet`. -/
noncomputable def fStarOmega
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    (v : RiemannSphere) → CotangentSpace 𝓘(ℝ, ℂ) v := fun v => by
  classical
  exact if hv : v ∈ f.regularValueSet then f.traceAt hnc hv om
        else (0 : CotangentSpace 𝓘(ℝ, ℂ) v)

/-! ## Apply at a regular vs. critical value -/

/-- At a regular value, `fStarOmega` reduces to `traceAt`. -/
@[simp] lemma fStarOmega_apply_of_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    f.fStarOmega hnc om v = f.traceAt hnc hv om := by
  classical
  unfold fStarOmega
  exact dif_pos hv

/-- At a non-regular value, `fStarOmega` is `0`. -/
@[simp] lemma fStarOmega_apply_of_not_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    {v : RiemannSphere} (hv : v ∉ f.regularValueSet) :
    f.fStarOmega hnc om v = (0 : CotangentSpace 𝓘(ℝ, ℂ) v) := by
  classical
  unfold fStarOmega
  exact dif_neg hv

/-! ## ℝ-linearity in the 1-form (pointwise) -/

@[simp] lemma fStarOmega_zero
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (v : RiemannSphere) :
    f.fStarOmega hnc (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) v
      = (0 : CotangentSpace 𝓘(ℝ, ℂ) v) := by
  classical
  by_cases hv : v ∈ f.regularValueSet
  · rw [f.fStarOmega_apply_of_regular hnc 0 hv, traceAt_zero]
  · exact f.fStarOmega_apply_of_not_regular hnc 0 hv

@[simp] lemma fStarOmega_add
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (om₁ om₂ : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (v : RiemannSphere) :
    f.fStarOmega hnc (om₁ + om₂) v
      = f.fStarOmega hnc om₁ v + f.fStarOmega hnc om₂ v := by
  classical
  by_cases hv : v ∈ f.regularValueSet
  · rw [f.fStarOmega_apply_of_regular hnc (om₁ + om₂) hv,
        f.fStarOmega_apply_of_regular hnc om₁ hv,
        f.fStarOmega_apply_of_regular hnc om₂ hv, traceAt_add]
  · rw [f.fStarOmega_apply_of_not_regular hnc (om₁ + om₂) hv,
        f.fStarOmega_apply_of_not_regular hnc om₁ hv,
        f.fStarOmega_apply_of_not_regular hnc om₂ hv, add_zero]

@[simp] lemma fStarOmega_smul
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (c : ℝ) (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (v : RiemannSphere) :
    f.fStarOmega hnc (c • om) v = c • f.fStarOmega hnc om v := by
  classical
  by_cases hv : v ∈ f.regularValueSet
  · rw [f.fStarOmega_apply_of_regular hnc (c • om) hv,
        f.fStarOmega_apply_of_regular hnc om hv, traceAt_smul]
  · rw [f.fStarOmega_apply_of_not_regular hnc (c • om) hv,
        f.fStarOmega_apply_of_not_regular hnc om hv, smul_zero]

end MeromorphicNonzero

end JacobianChallenge

end
