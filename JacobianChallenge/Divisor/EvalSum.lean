/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single

set_option linter.unusedSectionVars false

/-! # Divisor evaluation sum `∑ x ∈ supp D, (D x) • x`

For a topological additive group `X`, every divisor `D : Div X` evaluates to
an element of `X` by summing `(D x) • x` over the (finite) support of `D`.
This is the natural pairing between `Div X` and the underlying additive
structure on `X`.

Bundled as `Div.evalSumHom : Div X →+ X`, this provides a single
homomorphism that turns the analytic content of Abel's theorem on
elliptic functions (`TLDivSumHypothesis L` in
`Manifold/AbelHypothesisReductionComplexTorus.lean`) into a kernel-
containment statement: `range principalDivisorMap ⊆
AddMonoidHom.ker evalSumHom`.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge

namespace Div

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [AddCommGroup X]

/-- The *evaluation sum* of a divisor: `∑ x ∈ supp D, (D x) • x` in `X`. -/
noncomputable def evalSum (D : Div X) : X :=
  ∑ x ∈ D.supportFinset, ((D : X → ℤ) x) • x

/-- `evalSum` can be computed over any superset of the support: outside-
support points contribute `0` (zero `zsmul`). -/
lemma evalSum_eq_sum_of_supportFinset_subset
    {D : Div X} {S : Finset X} (hS : D.supportFinset ⊆ S) :
    evalSum D = ∑ x ∈ S, ((D : X → ℤ) x) • x := by
  classical
  unfold evalSum
  refine Finset.sum_subset hS ?_
  intro x _ hxS
  rw [apply_eq_zero_of_notMem_supportFinset hxS, zero_zsmul]

@[simp] lemma evalSum_zero : evalSum (0 : Div X) = 0 := by
  classical
  unfold evalSum
  have hempty : ((0 : Div X).supportFinset) = (∅ : Finset X) := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' := (mem_supportFinset (D := (0 : Div X)) (x := x)).1 hx
    apply hx'
    simp [Function.locallyFinsuppWithin.coe_zero]
  rw [hempty, Finset.sum_empty]

lemma evalSum_add (D₁ D₂ : Div X) :
    evalSum (D₁ + D₂) = evalSum D₁ + evalSum D₂ := by
  classical
  set S : Finset X :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have h1 : D₁.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h2 : D₂.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_right _ hx
  rw [evalSum_eq_sum_of_supportFinset_subset h12,
      evalSum_eq_sum_of_supportFinset_subset h1,
      evalSum_eq_sum_of_supportFinset_subset h2]
  have hpt : ∀ x : X,
      ((D₁ + D₂ : Div X) : X → ℤ) x • x
        = ((D₁ : X → ℤ) x) • x + ((D₂ : X → ℤ) x) • x := by
    intro x
    have h_coe : ((D₁ + D₂ : Div X) : X → ℤ) x
        = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
      simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    rw [h_coe, add_zsmul]
  simp_rw [hpt]
  exact Finset.sum_add_distrib

/-- The *evaluation sum* as an additive group homomorphism `Div X →+ X`. -/
noncomputable def evalSumHom : Div X →+ X where
  toFun := evalSum
  map_zero' := evalSum_zero
  map_add' := evalSum_add

@[simp] lemma evalSumHom_apply (D : Div X) : evalSumHom D = evalSum D := rfl

@[simp] lemma evalSum_neg (D : Div X) : evalSum (-D) = - evalSum D := by
  have h : evalSum (-D) = evalSumHom (X := X) (-D) := rfl
  rw [h, map_neg]
  simp [evalSumHom_apply]

@[simp] lemma evalSum_sub (D₁ D₂ : Div X) :
    evalSum (D₁ - D₂) = evalSum D₁ - evalSum D₂ := by
  have h : evalSum (D₁ - D₂) = evalSumHom (X := X) (D₁ - D₂) := rfl
  rw [h, map_sub]
  simp [evalSumHom_apply]

/-! ### `evalSum` on a singleton divisor

`Div.single x` lives at the single point `x` with value `1`, so its
evaluation sum is `1 • x = x`. -/

@[simp] lemma evalSum_single [DecidableEq X] (x : X) :
    evalSum (single x : Div X) = x := by
  classical
  unfold evalSum
  rw [supportFinset_single]
  simp [single_apply]

end Div

end JacobianChallenge
