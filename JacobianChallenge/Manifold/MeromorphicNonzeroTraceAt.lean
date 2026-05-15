/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CotangentPullbackAt
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import JacobianChallenge.Manifold.RiemannSphereRealManifold

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pointwise trace `f_*ω` at a regular value

For `f : MeromorphicNonzero X` non-constant and `v ∈ f.regularValueSet`,
the **trace** of a 1-form `om : SmoothOneForm 𝓘(ℝ, ℂ) X` at `v` is the
finite sum

  `traceAt f hnc v hv om := Σ_{p ∈ f⁻¹(v)} cotangentPullbackAt sheet_p.g v om`

where `sheet_p` is the local biholomorphism at the fibre point `p`.
Each summand is a `CotangentSpace 𝓘(ℝ, ℂ) v`-valued contribution; the
sum is the trace value at `v`.

This is the **pointwise** trace. Smoothness as a function of `v` is a
separate later layer (requires continuity of the local-sheet `.g` plus
sum continuity).

ℝ-linearity in the 1-form is automatic from
`cotangentPullbackAt_{zero, add, smul}` + `Finset.sum_{zero, add,
smul}`.

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

/-- The fiber `f⁻¹({v})` at a regular value `v`, as a `Finset X`. -/
noncomputable def fiberFinset
    (f : MeromorphicNonzero X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    Finset X :=
  (f.fiber_finite_of_mem_regularValueSet hv).toFinset

@[simp] lemma mem_fiberFinset_iff
    (f : MeromorphicNonzero X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) (x : X) :
    x ∈ f.fiberFinset hv ↔ f.toRiemannSphere x = v := by
  unfold fiberFinset
  exact Set.Finite.mem_toFinset _

/-- **Pointwise trace `f_*om` at a regular value `v`.** Finite sum of
per-sheet cotangent pullbacks over the fibre `f⁻¹({v})`. -/
noncomputable def traceAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    CotangentSpace 𝓘(ℝ, ℂ) v := by
  classical
  exact ∑ p ∈ (f.fiberFinset hv).attach,
    cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
      (f.localSheetData_at_regular hnc
        (f.mem_regularSet_of_preimage_regularValue hv
          ((f.mem_fiberFinset_iff hv p.val).mp p.property))).g
      v om

/-! ## ℝ-linearity in the 1-form -/

@[simp] lemma traceAt_zero
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    f.traceAt hnc hv (0 : SmoothOneForm 𝓘(ℝ, ℂ) X) = 0 := by
  unfold traceAt
  simp [cotangentPullbackAt_zero]

@[simp] lemma traceAt_add
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (om₁ om₂ : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    f.traceAt hnc hv (om₁ + om₂) = f.traceAt hnc hv om₁ + f.traceAt hnc hv om₂ := by
  classical
  unfold traceAt
  simp only [cotangentPullbackAt_add]
  exact Finset.sum_add_distrib

@[simp] lemma traceAt_smul
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (c : ℝ) (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    f.traceAt hnc hv (c • om) = c • f.traceAt hnc hv om := by
  classical
  unfold traceAt
  simp only [cotangentPullbackAt_smul]
  exact Finset.smul_sum.symm

end MeromorphicNonzero

end JacobianChallenge

end
