/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CriticalValuesFiniteUnconditional

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The regular-value set of `f.toRiemannSphere`

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold
`X`, the pole extension `f̃ := f.toRiemannSphere : X → RiemannSphere` is
a finite branched cover.  Its **critical-value set**
`f.criticalValues := f̃ '' f.criticalSet` is closed; for a *non-constant*
`f̃`, it is also finite (the unconditional `criticalValues_finite_unconditional`
chip).  The **regular-value set** is the complement
`f.regularValueSet := (f.criticalValues)ᶜ`.

This file defines `regularValueSet`, gives the basic openness lemma
under non-constancy, and supplies the cofinite-image hooks downstream
chips will consume for the level-set chain construction.

## What ships

* `MeromorphicNonzero.regularValueSet` — `(f.criticalValues)ᶜ`.

* `MeromorphicNonzero.regularValueSet_isOpen` — under non-constancy
  of `f.toRiemannSphere`, the regular-value set is open in
  `RiemannSphere = OnePoint ℂ` (T2, so finite ⇒ closed ⇒ complement open).

* `MeromorphicNonzero.criticalValues_finite` — under non-constancy,
  the critical-value set is finite (re-export of
  `criticalValues_finite_unconditional`).

* `MeromorphicNonzero.criticalValues_isClosed` — under non-constancy,
  the critical-value set is closed.

The substantive C3 (level-set chain) work consumes:
* A smooth path `β : SmoothPath 𝓘(ℝ, ℂ) RiemannSphere` whose image lies
  in `f.regularValueSet`.
* The local biholomorphism property of `f.toRiemannSphere` at every
  preimage of every regular value — supplied separately.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Regular-value set.** Complement of `criticalValues` in
`RiemannSphere`. -/
def regularValueSet (f : MeromorphicNonzero X) : Set RiemannSphere :=
  (f.criticalValues)ᶜ

@[simp] lemma regularValueSet_eq_compl_criticalValues (f : MeromorphicNonzero X) :
    f.regularValueSet = (f.criticalValues)ᶜ := rfl

lemma mem_regularValueSet (f : MeromorphicNonzero X) (v : RiemannSphere) :
    v ∈ f.regularValueSet ↔ v ∉ f.criticalValues := Iff.rfl

lemma notMem_criticalValues_of_mem_regularValueSet
    (f : MeromorphicNonzero X) {v : RiemannSphere}
    (hv : v ∈ f.regularValueSet) : v ∉ f.criticalValues := hv

lemma mem_regularValueSet_of_notMem_criticalValues
    (f : MeromorphicNonzero X) {v : RiemannSphere}
    (hv : v ∉ f.criticalValues) : v ∈ f.regularValueSet := hv

/-! ## Finiteness, closedness, openness under non-constancy -/

/-- **Critical values are finite** under non-constancy. Re-export of
the unconditional `criticalValues_finite_unconditional`. -/
theorem criticalValues_finite
    [ConnectedSpace X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    f.criticalValues.Finite :=
  JacobianChallenge.Manifold.criticalValues_finite_unconditional f hnc

/-- **Critical values are closed** in `RiemannSphere` under non-constancy.
`RiemannSphere = OnePoint ℂ` is T1 (in fact T2), and finite sets in T1
spaces are closed. -/
theorem criticalValues_isClosed
    [ConnectedSpace X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    IsClosed f.criticalValues :=
  (f.criticalValues_finite hnc).isClosed

/-- **Regular values are open** in `RiemannSphere` under non-constancy.
Complement of the closed critical-value set. -/
theorem regularValueSet_isOpen
    [ConnectedSpace X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere) :
    IsOpen f.regularValueSet := by
  rw [regularValueSet_eq_compl_criticalValues]
  exact (f.criticalValues_isClosed hnc).isOpen_compl

end MeromorphicNonzero

end JacobianChallenge

end
