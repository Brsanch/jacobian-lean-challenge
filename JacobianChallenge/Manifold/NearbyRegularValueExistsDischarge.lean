/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.NearbyRegularWitnessFromDecomposition
import JacobianChallenge.Manifold.ChartedSpaceOpenInfinite
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional
import JacobianChallenge.Manifold.CriticalValuesFiniteGeneral

set_option diagnostics.threshold 100
set_option maxHeartbeats 800000

/-! # Unconditional discharge of `NearbyRegularValueExists`

This file proves `NearbyRegularValueExists X Y` UNCONDITIONALLY by
composing:

1. `criticalValues_finite_general` (existing, unconditional) — for
   non-constant analytic `f`, the critical-value set is finite.
2. `open_nbhd_infinite_of_chartedSpace_complex` (zz333) — any open
   neighbourhood `V ∋ y₀` is infinite.
3. `preimages_locally_injective_of_notMem_criticalValues` (existing,
   private) + `deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood`
   (existing, private) — for `y'` not in critical values, the
   chart-pullback derivative is nonzero at every preimage.

Together: V is infinite, criticalValues f ∪ {y₀} is finite, so the
complement V \ (criticalValues f ∪ {y₀}) is non-empty. Pick y' there;
y' ∈ V, y' ≠ y₀, and y' is a regular value (chart-pullback deriv ≠ 0).

This is the UNCONDITIONAL closure of zz332's named open hypothesis,
removing one of the open inputs from the path to item 14.

No `sorry`, no `axiom`.
-/

open scoped Manifold ContDiff
open Set Filter Topology Metric

noncomputable section

namespace JacobianChallenge

universe u v

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

/-- **Unconditional discharge of `NearbyRegularValueExists X Y`.**
For non-constant analytic `f`, every open `V ∋ y₀` contains a regular
value `y' ≠ y₀`. -/
theorem nearbyRegularValueExists_holds_unconditional :
    NearbyRegularValueExists X Y := by
  intro f hf hnc y₀ V hV_open hy₀_in
  -- Critical values are finite.
  have h_cv_fin : (JacobianChallenge.Manifold.criticalValuesGeneral f).Finite :=
    JacobianChallenge.Manifold.criticalValues_finite_general f hf hnc
  -- V is infinite (zz333).
  have hV_inf : V.Infinite :=
    open_nbhd_infinite_of_chartedSpace_complex hV_open hy₀_in
  -- The set to avoid: criticalValuesGeneral f ∪ {y₀}, which is finite.
  set bad : Set Y := JacobianChallenge.Manifold.criticalValuesGeneral f ∪ {y₀}
  have h_bad_fin : bad.Finite := h_cv_fin.union (Set.finite_singleton _)
  -- V \ bad is infinite (V infinite, bad finite).
  have h_diff_inf : (V \ bad).Infinite := hV_inf.diff h_bad_fin
  -- In particular non-empty.
  obtain ⟨y', hy'_in_diff⟩ := h_diff_inf.nonempty
  have hy'_V : y' ∈ V := hy'_in_diff.1
  have hy'_not_bad : y' ∉ bad := hy'_in_diff.2
  -- Extract: y' ≠ y₀ and y' ∉ criticalValuesGeneral f.
  have hy'_ne : y' ≠ y₀ := by
    intro h
    apply hy'_not_bad
    right; exact h
  have hy'_reg : y' ∉ JacobianChallenge.Manifold.criticalValuesGeneral f := by
    intro h
    apply hy'_not_bad
    left; exact h
  -- Use the deriv-nonzero discharge for non-critical values.
  refine ⟨y', hy'_V, hy'_ne, ?_⟩
  intro x hx
  -- hx : x ∈ f ⁻¹' {y'}, i.e., f x = y'.
  have hfx_eq : f x = y' := hx
  -- y' is not a critical value, so f is locally injective at x.
  have h_inj_exists : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
    -- Inline the (private) `preimages_locally_injective_of_notMem_criticalValues`
    -- argument: x ∉ criticalSetGeneral f (else y' = f x ∈ criticalValuesGeneral f).
    have hx_not_crit : x ∉ JacobianChallenge.Manifold.criticalSetGeneral f := by
      intro hx_crit
      apply hy'_reg
      exact ⟨x, hx_crit, hfx_eq⟩
    -- criticalSetGeneral = { x | ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U }; complement gives the witness.
    by_contra h
    apply hx_not_crit
    show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
    exact h
  -- Apply the deriv-nonzero lemma at f x = y'.
  have h_deriv_at_fx :
      deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    JacobianChallenge.ContMDiff.Owed.degree.deriv_chart_pullback_ne_zero_of_inj_on_neighbourhood
      hf hnc x h_inj_exists
  rw [← hfx_eq]
  exact h_deriv_at_fx

end JacobianChallenge

end
