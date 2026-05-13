/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.RamificationSumRegular
import JacobianChallenge.Manifold.RamificationSumEqualsDegree
import JacobianChallenge.Manifold.RamificationSumEqualsDegreeUnconditional
import JacobianChallenge.Manifold.FibresFiniteUnconditional

set_option diagnostics.threshold 100

/-! # `degreeFiber f = 1` ⇒ singleton fibres (conditional on
ramification-sum-equals-degree)

This is the first concrete step toward zz325's
`DegreeOneIsBiholomorphic_RS`: under the named conditional input
`ramificationSumEqualsDegree_statement X RS` (which holds
unconditionally up to a single named hypothesis
`NearbyRegularWitnessHypothesis X RS`), a non-constant ContMDiff
map `f : X → RS` with `degreeFiber = 1` has *singleton fibres at
every value*.

## Argument

For any `y : Y`, the fibre `f ⁻¹' {y}` is finite (`FibresFinite`),
and the sum of `manifoldRamificationIndex f x` over this fibre equals
`degreeFiber f` (the conditional ramification-sum-equals-degree
statement). Each summand is ≥ 1 (`manifoldRamificationIndex_pos_unconditional`).
If the sum equals 1, then there is exactly one summand and that
summand equals 1: the fibre is a singleton.

## What ships

* `fibre_singleton_of_degreeFiber_eq_one` — under
  `ramificationSumEqualsDegree_statement X Y`, the fibre `f ⁻¹' {y}`
  is a singleton for every `y` when `degreeFiber f = 1`.

No `sorry`, no `axiom`. Conditional on the named input; that input
itself is unconditional modulo `NearbyRegularWitnessHypothesis X Y`.
-/

open scoped Manifold ContDiff
open Finset

noncomputable section

namespace JacobianChallenge

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **`degreeFiber = 1` forces every fibre to be a singleton (with
ramification index 1).** Conditional on the
`ramificationSumEqualsDegree_statement X Y` named hypothesis. -/
theorem fibre_card_eq_one_of_degreeFiber_eq_one
    (h_RS : JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y)
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    (h_deg : JacobianChallenge.ContMDiff.degreeFiber f hf = 1)
    (y : Y) :
    (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset.card = 1 := by
  -- Sum of multiplicities over the fibre = degreeFiber = 1.
  have hSum :
      (∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
          JacobianChallenge.Manifold.manifoldRamificationIndex f x : ℕ) = 1 := by
    rw [h_RS f hf hnc y, h_deg]
  -- Each summand is ≥ 1: by unconditional positivity at every fibre point.
  have hPos :
      ∀ x ∈ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
        1 ≤ JacobianChallenge.Manifold.manifoldRamificationIndex f x := by
    intro x hx
    have hxy : f x = y := by
      have := (Set.Finite.mem_toFinset _).mp hx
      simpa using this
    exact JacobianChallenge.Manifold.manifoldRamificationIndex_pos_unconditional hf hnc hxy
  -- Sum ≥ card by summand ≥ 1.
  have hCard_le_sum :
      (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset.card ≤
        ∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
          JacobianChallenge.Manifold.manifoldRamificationIndex f x := by
    calc (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset.card
        = ∑ _x ∈ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset, (1 : ℕ) := by simp
      _ ≤ ∑ x ∈ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
          JacobianChallenge.Manifold.manifoldRamificationIndex f x :=
        Finset.sum_le_sum hPos
  -- Card ≥ 1 because the fibre is non-empty.
  have hCard_ge_one :
      1 ≤ (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset.card := by
    -- Non-emptiness of the fibre: non-constancy gives every value is attained.
    rw [Finset.one_le_card]
    -- Use the non-constant-map-from-compact-connected-source surjects on Y
    -- argument. Mathlib has `IsCompact.image_isOpen_eq_of_isConnected` style
    -- results; here we directly use the fact that f is surjective for any
    -- non-constant ContMDiff on a compact connected source mapping to a
    -- compact connected target. We dispatch via the fibre's image-preimage
    -- structure.
    -- For now, derive non-emptiness from the fact that `∑ … = 1 ≠ 0`.
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hSum
    simp at hSum
  -- Card ≤ sum = 1 and card ≥ 1 forces card = 1.
  have hCard_le_one : (JacobianChallenge.ContMDiff.Owed.degree.fibres_finite_statement_holds_unconditional f hf hnc y).toFinset.card ≤ 1 := by
    have := hCard_le_sum.trans (le_of_eq hSum)
    exact this
  exact le_antisymm hCard_le_one hCard_ge_one

end JacobianChallenge

end
