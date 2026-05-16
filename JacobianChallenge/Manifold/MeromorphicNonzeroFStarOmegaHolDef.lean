/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroHolTraceAt

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `fStarOmegaHol`: holomorphic trace as a `v`-varying section

Holomorphic-side analogue of `fStarOmega`
(`Manifold/MeromorphicNonzeroFStarOmegaDef.lean`). For
`f : MeromorphicNonzero X` non-constant and
`α : HolomorphicOneForm X`, the **holomorphic pushforward 1-form**
`f_*α` is canonically defined only at regular values: at
`v ∈ f.regularValueSet`, its value is the pointwise holomorphic trace
`f.holTraceAt hnc hv α : CotangentSpace 𝓘(ℂ, ℂ) v`. Off the
regular-value set the pushforward 1-form has no canonical value
(critical values may have a single sheet of ramification index ≥ 2
where the holomorphic trace formula breaks down).

This file packages the pointwise holomorphic trace as a `v`-varying
section
`fStarOmegaHol f hnc α : (v : RiemannSphere) → CotangentSpace 𝓘(ℂ, ℂ) v`,
returning the trace at regular values and `0` elsewhere (junk).

The `0` choice off the regular-value set is convenient — it gives a
total function so the downstream "holomorphic-on-regularValueSet"
packaging needs only local agreement.

ℂ-linearity in the 1-form descends pointwise from
`MeromorphicNonzero.holTraceAt_{zero, add, smul}`.

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

/-- **`f_*α` as a `v`-varying section.** At a regular value `v`,
returns `f.holTraceAt hnc hv α`. Off the regular-value set, returns `0`
(junk). Total dependent function so downstream
holomorphicity-on-`regularValueSet` packaging needs only local
agreement. -/
noncomputable def fStarOmegaHol
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X) :
    (v : RiemannSphere) → CotangentSpace 𝓘(ℂ, ℂ) v := fun v => by
  classical
  exact if hv : v ∈ f.regularValueSet then f.holTraceAt hnc hv α
        else (0 : CotangentSpace 𝓘(ℂ, ℂ) v)

/-! ## Apply at a regular vs. critical value -/

/-- At a regular value, `fStarOmegaHol` reduces to `holTraceAt`. -/
@[simp] lemma fStarOmegaHol_apply_of_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    f.fStarOmegaHol hnc α v = f.holTraceAt hnc hv α := by
  classical
  unfold fStarOmegaHol
  exact dif_pos hv

/-- At a non-regular value, `fStarOmegaHol` is `0`. -/
@[simp] lemma fStarOmegaHol_apply_of_not_regular
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v : RiemannSphere} (hv : v ∉ f.regularValueSet) :
    f.fStarOmegaHol hnc α v = (0 : CotangentSpace 𝓘(ℂ, ℂ) v) := by
  classical
  unfold fStarOmegaHol
  exact dif_neg hv

/-! ## ℂ-linearity in the 1-form (pointwise) -/

@[simp] lemma fStarOmegaHol_zero
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (v : RiemannSphere) :
    f.fStarOmegaHol hnc (0 : HolomorphicOneForm X) v
      = (0 : CotangentSpace 𝓘(ℂ, ℂ) v) := by
  classical
  by_cases hv : v ∈ f.regularValueSet
  · rw [f.fStarOmegaHol_apply_of_regular hnc 0 hv, holTraceAt_zero]
  · exact f.fStarOmegaHol_apply_of_not_regular hnc 0 hv

@[simp] lemma fStarOmegaHol_add
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α₁ α₂ : HolomorphicOneForm X)
    (v : RiemannSphere) :
    f.fStarOmegaHol hnc (α₁ + α₂) v
      = f.fStarOmegaHol hnc α₁ v + f.fStarOmegaHol hnc α₂ v := by
  classical
  by_cases hv : v ∈ f.regularValueSet
  · rw [f.fStarOmegaHol_apply_of_regular hnc (α₁ + α₂) hv,
        f.fStarOmegaHol_apply_of_regular hnc α₁ hv,
        f.fStarOmegaHol_apply_of_regular hnc α₂ hv, holTraceAt_add]
  · rw [f.fStarOmegaHol_apply_of_not_regular hnc (α₁ + α₂) hv,
        f.fStarOmegaHol_apply_of_not_regular hnc α₁ hv,
        f.fStarOmegaHol_apply_of_not_regular hnc α₂ hv, add_zero]

@[simp] lemma fStarOmegaHol_smul
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (c : ℂ) (α : HolomorphicOneForm X)
    (v : RiemannSphere) :
    f.fStarOmegaHol hnc (c • α) v = c • f.fStarOmegaHol hnc α v := by
  classical
  by_cases hv : v ∈ f.regularValueSet
  · rw [f.fStarOmegaHol_apply_of_regular hnc (c • α) hv,
        f.fStarOmegaHol_apply_of_regular hnc α hv, holTraceAt_smul]
  · rw [f.fStarOmegaHol_apply_of_not_regular hnc (c • α) hv,
        f.fStarOmegaHol_apply_of_not_regular hnc α hv, smul_zero]

end MeromorphicNonzero

end JacobianChallenge

end
