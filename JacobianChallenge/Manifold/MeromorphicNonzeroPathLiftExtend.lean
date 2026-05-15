/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import Mathlib.Topology.Piecewise

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Extension of a continuous lift across one local sheet

Given a continuous lift `γ : ℝ → X` of `β` on `Icc a b`, and a regular
anchor `x_anchor` with `γ b ∈ sheet.U` and `β` mapping `Icc b c` into
`sheet.V`, the piecewise function

  `γ'(t) := if t ≤ b then γ t else sheet.g (β t)`

is `ContinuousOn (Icc a c)` and lifts `β` on `Icc a c`.

This is the single-step extension lemma — the inductive step for the
global path-lift gluing across the partition (chip 17).

## What ships

* `MeromorphicNonzero.extend_lift_across_sheet` — the headline
  extension theorem.

No `sorry`, no `axiom`. -/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Extension of a continuous lift across one local sheet.** -/
theorem extend_lift_across_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere} (hβ_cont : Continuous β)
    {γ : ℝ → X} (hγ_cont : Continuous γ)
    {a b c : ℝ} (hab : a ≤ b) (_hbc : b ≤ c)
    (hγ_lift : ∀ t ∈ Icc a b, f.toRiemannSphere (γ t) = β t)
    {x_anchor : X} (hx_anchor_reg : x_anchor ∈ f.regularSet)
    (hβ_in_V : ∀ t ∈ Icc b c, β t ∈
      (f.localSheetData_at_regular hnc hx_anchor_reg).V)
    (hγb_in_U : γ b ∈ (f.localSheetData_at_regular hnc hx_anchor_reg).U) :
    ∃ γ' : ℝ → X,
      ContinuousOn γ' (Icc a c) ∧
      (∀ t ∈ Iic b, γ' t = γ t) ∧
      (∀ t ∈ Icc a c, f.toRiemannSphere (γ' t) = β t) := by
  classical
  set sheet := f.localSheetData_at_regular hnc hx_anchor_reg with hsheet_def
  -- The piecewise function.
  let γ' : ℝ → X := fun t => if t ≤ b then γ t else sheet.g (β t)
  refine ⟨γ', ?_, ?_, ?_⟩
  · -- ContinuousOn γ' (Icc a c).
    -- Use `ContinuousOn.if` with predicate `p t := t ≤ b`.
    -- frontier {t | t ≤ b} = {b}. closure {t | t ≤ b} = Iic b.
    -- closure {t | ¬ (t ≤ b)} = Ici b.
    have h_frontier : frontier {t : ℝ | t ≤ b} = {b} := by
      have h1 : {t : ℝ | t ≤ b} = Iic b := rfl
      rw [h1, frontier_Iic]
    -- ht: at frontier (= {b}), γ b = sheet.g (β b).
    have hγ_lift_b : f.toRiemannSphere (γ b) = β b :=
      hγ_lift b ⟨hab, le_refl b⟩
    have h_agree_at_b : γ b = sheet.g (β b) := by
      have h_sheet_b : sheet.g (β b) = γ b := by
        have : sheet.g (f.toRiemannSphere (γ b)) = γ b :=
          sheet.leftInvOn hγb_in_U
        rw [← hγ_lift_b]
        exact this
      exact h_sheet_b.symm
    -- ContinuousOn γ (Icc a c ∩ closure {t | t ≤ b}) = ContinuousOn γ (Icc a c ∩ Iic b).
    have hf_cont : ContinuousOn γ (Icc a c ∩ closure {t : ℝ | t ≤ b}) :=
      hγ_cont.continuousOn
    -- ContinuousOn (sheet.g ∘ β) (Icc a c ∩ closure {t | ¬ (t ≤ b)}) =
    --   ContinuousOn (sheet.g ∘ β) (Icc a c ∩ Ici b).
    -- We have β maps [b, c] into sheet.V, and Icc a c ∩ Ici b = Icc b c.
    have h_set_eq : Icc a c ∩ closure {t : ℝ | ¬ (t ≤ b)} = Icc b c ∩ Icc a c := by
      have h_closure : closure {t : ℝ | ¬ (t ≤ b)} = Ici b := by
        have : {t : ℝ | ¬ (t ≤ b)} = Ioi b := by ext t; simp
        rw [this, closure_Ioi]
      rw [h_closure]
      ext t
      simp [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨hac1, hac2⟩, hbtle⟩
        exact ⟨⟨hbtle, hac2⟩, hac1, hac2⟩
      · rintro ⟨⟨hbtle, hbc2⟩, hac1, hac2⟩
        exact ⟨⟨hac1, hac2⟩, hbtle⟩
    have hg_cont : ContinuousOn (fun t => sheet.g (β t))
        (Icc a c ∩ closure {t : ℝ | ¬ (t ≤ b)}) := by
      rw [h_set_eq]
      have h_inner : ContinuousOn sheet.g sheet.V := sheet.g_continuousOn
      have h_mapsTo : MapsTo β (Icc b c ∩ Icc a c) sheet.V := by
        intro t ht
        exact hβ_in_V t ht.1
      exact h_inner.comp hβ_cont.continuousOn h_mapsTo
    -- Now apply ContinuousOn.if.
    have h_ht : ∀ a' ∈ Icc a c ∩ frontier {t : ℝ | t ≤ b}, γ a' = sheet.g (β a') := by
      intro a' ha'
      have ha'_b : a' = b := by
        have : a' ∈ frontier {t : ℝ | t ≤ b} := ha'.2
        rw [h_frontier] at this
        exact this
      rw [ha'_b]
      exact h_agree_at_b
    exact ContinuousOn.if h_ht hf_cont hg_cont
  · -- γ' t = γ t for t ≤ b.
    intro t htb
    have htb_le : t ≤ b := htb
    show (if t ≤ b then γ t else sheet.g (β t)) = γ t
    rw [if_pos htb_le]
  · -- f.toRiemannSphere (γ' t) = β t for t ∈ Icc a c.
    intro t htac
    show f.toRiemannSphere (if t ≤ b then γ t else sheet.g (β t)) = β t
    by_cases htb : t ≤ b
    · rw [if_pos htb]
      exact hγ_lift t ⟨htac.1, htb⟩
    · rw [if_neg htb]
      have htb' : b ≤ t := le_of_lt (lt_of_not_ge htb)
      have ht_bc : t ∈ Icc b c := ⟨htb', htac.2⟩
      exact sheet.rightInvOn (hβ_in_V t ht_bc)

end MeromorphicNonzero

end JacobianChallenge

end
