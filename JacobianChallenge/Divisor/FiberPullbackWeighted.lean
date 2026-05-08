/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor
import JacobianChallenge.Divisor.Single
import JacobianChallenge.Divisor.FiberSumWeighted
import JacobianChallenge.Jacobian

set_option diagnostics.threshold 100

/-! # Weighted `Pic⁰`-level pullback (ZZ179c)

Mirror of `Divisor/FiberPullback.lean` for the multiplicity-weighted
fibre sum `Div.fiberSumWeighted` (`Divisor/FiberSumWeighted.lean`).

The weighted construction is the honest classical pullback: with
`e := manifoldRamificationIndex f` and the analytic identity
`∑_{x ∈ f⁻¹{y}} e_x(f) = deg(f)` constant in `y` on regular fibres,
it sends `Div⁰ Y → Div⁰ X` without the false "every fibre has the same
cardinality" hypothesis required by the unweighted version. See
`HANDOFF_ZZ177_PULLBACK_BLOCKER.md` for the full context.

## Contents

* `Div.degree_fiberSumWeighted` — the degree of `fiberSumWeighted e D` is
  `∑_{y ∈ supp D} D(y) · (∑_{x ∈ f⁻¹{y}} e x : ℤ)`.
* `Div.fiberSumWeighted_mem_Div0_of_const_total_weight` — under the
  classical "constant total weight per fibre" hypothesis, `fiberSumWeighted`
  sends `Div⁰ Y` into `Div⁰ X`.
* `Pic0.divPullbackWeighted` — descent to `Div0 Y →+ Div0 X`.
* `Pic0.pullbackWeighted` — descent to `Pic0 Y →+ Pic0 X` (with the
  placeholder `PrincDiv = ⊥`, this descent is automatic, mirroring the
  unweighted `Pic0.pullback`).

## Anti-cheat note

The hypothesis `hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N` replaces
the unweighted version's `hN : ∀ y, (hf y).toFinset.card = N`. Both are
load-bearing in the same way: they turn the weighted-degree formula into
`N · D.degree`, which is `0` for `D ∈ Div⁰`. The classical fact that
makes `hN_total` true unconditionally for `e := manifoldRamificationIndex f`
on regular fibres is the planar k-fold multiplicity theorem
(`localKFoldMultiplicity_preimage_card_fully_unconditional`) lifted to
the manifold via chart pullback. -/

namespace JacobianChallenge

namespace Div

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X]

/-- The degree of `fiberSumWeighted f hf e D` is the weighted sum
`∑_{y ∈ supp D} D(y) · (∑_{x ∈ f⁻¹{y}} e x : ℤ)`. -/
lemma degree_fiberSumWeighted
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (D : Div Y) :
    (Div.fiberSumWeighted f hf e D).degree
      = ∑ y ∈ D.supportFinset,
          D y * ((∑ x ∈ (hf y).toFinset, e x : ℕ) : ℤ) := by
  classical
  -- Reduce `degree` to `degreeHom`.
  have hLHS : (Div.fiberSumWeighted f hf e D).degree
      = degreeHom (X := X) (Div.fiberSumWeighted f hf e D : Div X) := rfl
  rw [hLHS]
  -- Unfold the bundled hom application.
  have hsum : (Div.fiberSumWeighted f hf e D : Div X)
      = ∑ y ∈ D.supportFinset,
          D y • (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x) := by
    show Div.fiberSumWeightedFun f hf e D = _
    rfl
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [map_zsmul, degreeHom_apply]
  -- Compute `(∑ x ∈ fibre, (e x : ℤ) • single x).degree = ∑ x, e x` (cast to ℤ).
  have hfib :
      (∑ x ∈ (hf y).toFinset, (e x : ℤ) • (Div.single x : Div X)).degree
        = ((∑ x ∈ (hf y).toFinset, e x : ℕ) : ℤ) := by
    have hsub :
        (∑ x ∈ (hf y).toFinset, (e x : ℤ) • (Div.single x : Div X)).degree
          = degreeHom (X := X)
              (∑ x ∈ (hf y).toFinset, (e x : ℤ) • Div.single x) := rfl
    rw [hsub, map_sum]
    -- Each summand: `degreeHom ((e x : ℤ) • single x) = (e x : ℤ) * 1 = (e x : ℤ)`.
    have heach : ∀ x ∈ (hf y).toFinset,
        degreeHom (X := X) ((e x : ℤ) • (Div.single x : Div X))
          = (e x : ℤ) := by
      intro x _
      rw [map_zsmul, degreeHom_apply, degree_single]
      rw [smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl heach]
    -- `∑ x ∈ S, (e x : ℤ) = ((∑ x ∈ S, e x : ℕ) : ℤ)`.
    push_cast
    rfl
  rw [hfib, smul_eq_mul]

/-- If the total weighted multiplicity over each fibre is the *same* `N`,
then `Div.fiberSumWeighted f hf e` sends `Div⁰ Y` into `Div⁰ X`. -/
lemma fiberSumWeighted_mem_Div0_of_const_total_weight
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N)
    {D : Div Y} (hD : D ∈ Div0 Y) :
    Div.fiberSumWeighted f hf e D ∈ Div0 X := by
  classical
  rw [JacobianChallenge.mem_Div0_iff, degree_fiberSumWeighted]
  -- Goal: `∑ y ∈ supp D, D y * ((∑ x ∈ fibre, e x : ℕ) : ℤ) = 0`.
  have hcast : ∀ y ∈ D.supportFinset,
      D y * ((∑ x ∈ (hf y).toFinset, e x : ℕ) : ℤ)
        = D y * (N : ℤ) := by
    intro y _
    rw [hN_total y]
  rw [Finset.sum_congr rfl hcast]
  rw [← Finset.sum_mul]
  have hdeg : ∑ y ∈ D.supportFinset, (D : Y → ℤ) y = D.degree := rfl
  rw [hdeg]
  rw [(JacobianChallenge.mem_Div0_iff D).mp hD, zero_mul]

end Div

/-! ### `Div0`-level and `Pic0`-level weighted pullback -/

namespace Pic0

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [DecidableEq X]

/-- The constant-total-weight version of the divisor pullback, descending
`Div.fiberSumWeighted` to `Div0 Y →+ Div0 X`. -/
noncomputable def divPullbackWeighted
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N) :
    Div0 Y →+ Div0 X :=
  AddMonoidHom.codRestrict
    ((Div.fiberSumWeighted f hf e).comp (Div0 Y).subtype) (Div0 X)
    (fun D =>
      Div.fiberSumWeighted_mem_Div0_of_const_total_weight f hf e N hN_total D.2)

/-- Compute the underlying `Div X`-element of `divPullbackWeighted`. -/
@[simp] lemma divPullbackWeighted_coe
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N) (D : Div0 Y) :
    ((divPullbackWeighted f hf e N hN_total D : Div0 X) : Div X)
      = Div.fiberSumWeighted f hf e (D : Div Y) := rfl

/-- Promote the weighted pullback to `Pic⁰ Y →+ Pic⁰ X`. With the
placeholder `PrincDiv = ⊥` the descent through the quotient is
automatic. -/
noncomputable def pullbackWeighted
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N) :
    Pic0 Y →+ Pic0 X := by
  refine QuotientAddGroup.map
    ((PrincDiv Y).addSubgroupOf (Div0 Y))
    ((PrincDiv X).addSubgroupOf (Div0 X))
    (divPullbackWeighted f hf e N hN_total) ?_
  intro D hD
  have hBot : (PrincDiv Y).addSubgroupOf (Div0 Y) = ⊥ := by
    unfold PrincDiv
    simp [AddSubgroup.addSubgroupOf]
  rw [hBot, AddSubgroup.mem_bot] at hD
  subst hD
  rw [AddSubgroup.mem_comap]
  rw [map_zero]
  exact AddSubgroup.zero_mem _

@[simp] lemma pullbackWeighted_mk
    (f : X → Y) (hf : ∀ y, (f ⁻¹' {y}).Finite) (e : X → ℕ) (N : ℕ)
    (hN_total : ∀ y, (∑ x ∈ (hf y).toFinset, e x) = N) (D : Div0 Y) :
    pullbackWeighted f hf e N hN_total (QuotientAddGroup.mk D : Pic0 Y)
      = (QuotientAddGroup.mk
          (divPullbackWeighted f hf e N hN_total D) : Pic0 X) := rfl

end Pic0

end JacobianChallenge
