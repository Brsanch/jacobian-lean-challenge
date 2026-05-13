/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DegreeOneInjectiveFibres

set_option diagnostics.threshold 100

/-! # `degreeFiber f = 1` ⇒ `f` is injective (conditional on RS-EQ-DEG)

zz326 showed: under `ramificationSumEqualsDegree_statement X Y`,
`degreeFiber f = 1` forces every fibre `f ⁻¹' {y}` to have
`toFinset.card = 1`. This file translates the singleton-fibre
conclusion into the standard `Function.Injective f` statement.

The argument: for `x₁, x₂` with `f x₁ = f x₂ = y`, both lie in
`f ⁻¹' {y}`. Since the fibre has cardinality 1 as a finite set, it
is a singleton, so `x₁ = x₂`.

No `sorry`, no `axiom`. Conditional on the same named input as zz326.
-/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **`degreeFiber f = 1` ⇒ `f` is injective.** Conditional on
`ramificationSumEqualsDegree_statement X Y`. -/
theorem injective_of_degreeFiber_eq_one
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_deg : JacobianChallenge.ContMDiff.degreeFiber f hf = 1) :
    Function.Injective f := by
  intro x₁ x₂ hxy
  -- Both `x₁` and `x₂` lie in `f ⁻¹' {f x₁}`.
  set y : Y := f x₁ with hy
  have hx₁ : x₁ ∈ f ⁻¹' {y} := by simp [hy]
  have hx₂ : x₂ ∈ f ⁻¹' {y} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact hxy.symm
  -- The fibre is finite (`fibres_finite_statement_holds_unconditional`).
  set hfib :=
    JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional
      f hf hnc y
  -- By zz326, its toFinset has cardinality 1, hence is a singleton.
  have hCard : hfib.toFinset.card = 1 :=
    fibre_card_eq_one_of_degreeFiber_eq_one h_RS hf hnc h_deg y
  -- Get the singleton element a, and show x₁ = a = x₂.
  rw [Finset.card_eq_one] at hCard
  obtain ⟨a, ha⟩ := hCard
  have hx₁_mem : x₁ ∈ hfib.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hx₁
  have hx₂_mem : x₂ ∈ hfib.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hx₂
  rw [ha] at hx₁_mem hx₂_mem
  simp at hx₁_mem hx₂_mem
  rw [hx₁_mem, hx₂_mem]

end JacobianChallenge

end
