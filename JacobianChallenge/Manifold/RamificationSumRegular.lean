/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Analytic.Order
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.RamificationIndexPositive
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.ChartOverlapPropagationDischarge
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge
import JacobianChallenge.Manifold.Degree
import JacobianChallenge.Manifold.FibresFiniteUnconditional

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Regular-value case of the ramification sum formula

Three unconditional results around the manifold ramification index on a
`RegularValueWitnessReg f`:

* `manifoldRamificationIndex_pos_unconditional` — drops the
  `PerChartNonConstancyHypothesis X Y` from
  `manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy` (a fibre
  point of a non-constant analytic map between compact connected complex
  1-manifolds has ramification index ≥ 1).

* `manifoldRamificationIndex_eq_one_at_regularWitnessReg_preimage` — at
  every preimage of the chosen value of a `RegularValueWitnessReg`, the
  manifold ramification index equals `1`. The `is_regular` field gives the
  chart-pullback derivative nonzero; mathlib's
  `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` then forces the
  analytic order to be `1`, hence the `toNat` is `1`.

* `sum_manifoldRamificationIndex_eq_card_of_regularWitnessReg` — the
  regular-value case of the ramification sum formula: for a
  `RegularValueWitnessReg f`,
  `∑ x ∈ w.fiber_finite.toFinset, manifoldRamificationIndex f x = w.card`.
  This is the Riemann-Hurwitz total-weight identity restricted to regular
  values, where every preimage contributes weight `1` and the sum is just
  the cardinality of the fibre.

No `sorry`, no `axiom`, no new named hypotheses. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace Manifold

universe u v

/-! ## Unconditional positivity of the ramification index

Compose `manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy`
(which consumes a `PerChartNonConstancyHypothesis X Y`) with
`perChartNonConstancy_of_clopennessOfLocallyConst` (which produces one from
a `ClopennessOfLocallyConstHypothesis X Y`) and `clopennessOfLocallyConst_holds`
(unconditional). -/

/-- **Unconditional positivity of the ramification index at fibre points.**
For non-constant `C^ω` `f : X → Y` between compact connected complex
1-manifolds and any preimage `x` of `y = f x`,
`1 ≤ manifoldRamificationIndex f x`. -/
theorem manifoldRamificationIndex_pos_unconditional
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    {x : X} {y : Y} (hxy : f x = y) :
    1 ≤ manifoldRamificationIndex f x := by
  have H :
      JacobianChallenge.ContMDiff.Owed.degree.PerChartNonConstancyHypothesis X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.perChartNonConstancy_of_clopennessOfLocallyConst
      JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  exact manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
    H hf hnc hxy

/-! ## Index equals `1` at a regular-witness preimage

The `is_regular` field of a `RegularValueWitnessReg f` certifies that at every
preimage `x` of the chosen value, the chart-pullback `F := (chartAt ℂ w.value)
∘ f ∘ (chartAt ℂ x).symm` has nonzero derivative at `(chartAt ℂ x) x`. The
chart-pullback is analytic there (because `f` is `C^ω`), so mathlib's
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` gives the analytic
order of `F - F z₀` at `z₀` exactly `1`, hence
`manifoldRamificationIndex f x = (1 : ℕ∞).toNat = 1`. -/

/-- **Ramification index `= 1` at a regular-witness preimage.**
For `w : RegularValueWitnessReg f` and `x ∈ f ⁻¹' {w.toWitness.value}`,
`manifoldRamificationIndex f x = 1`. -/
theorem manifoldRamificationIndex_eq_one_at_regularWitnessReg_preimage
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (w : RegularValueWitnessReg f)
    {x : X} (hx : x ∈ f ⁻¹' {w.toWitness.value}) :
    manifoldRamificationIndex f x = 1 := by
  classical
  -- f x = w.toWitness.value
  have hfx_eq : f x = w.toWitness.value := hx
  -- Set up the chart pullback using f x (this is what manifoldRamificationIndex uses).
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  -- F is analytic at z₀.
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback
      hf x
  -- The regular-witness certificate uses chartAt ℂ w.toWitness.value, but f x =
  -- w.toWitness.value, so the two coincide after a rewrite.
  have h_deriv_at_value :
      deriv ((chartAt ℂ w.toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) ≠ 0 :=
    w.is_regular x hx
  have h_deriv_ne : deriv F z₀ ≠ 0 := by
    show deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0
    rw [hfx_eq]
    exact h_deriv_at_value
  -- Mathlib: deriv ≠ 0 ⇒ analyticOrderAt (F - F z₀) z₀ = 1.
  have h_ord :
      analyticOrderAt (fun z => F z - F z₀) z₀ = (1 : ℕ∞) :=
    hF_an.analyticOrderAt_sub_eq_one_of_deriv_ne_zero h_deriv_ne
  -- Unfold the index. `manifoldRamificationIndex_eq` gives the chart-pullback form;
  -- the lambda and base-point match `(fun z => F z - F z₀)` and `z₀` definitionally
  -- (since `F` and `z₀` were introduced via `set`).
  have h_unfold : manifoldRamificationIndex f x
      = (analyticOrderAt (fun z => F z - F z₀) z₀).toNat :=
    manifoldRamificationIndex_eq f x
  rw [h_unfold, h_ord]
  rfl

/-! ## Regular-value case of the ramification sum formula

With every preimage contributing weight `1` and the fibre finite (carried by
`w.toWitness.fiber_finite`), the sum of ramification indices over the fibre
is just the cardinality of the fibre, which is `w.card`. -/

/-- **Regular-value case of the ramification sum formula.**
For `w : RegularValueWitnessReg f`,
`∑ x ∈ w.toWitness.fiber_finite.toFinset, manifoldRamificationIndex f x = w.card`. -/
theorem sum_manifoldRamificationIndex_eq_card_of_regularWitnessReg
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (w : RegularValueWitnessReg f) :
    ∑ x ∈ w.toWitness.fiber_finite.toFinset, manifoldRamificationIndex f x =
      w.card := by
  classical
  -- Each summand is 1 (regular-witness preimage ⇒ index = 1).
  have h_each : ∀ x ∈ w.toWitness.fiber_finite.toFinset,
      manifoldRamificationIndex f x = 1 := by
    intro x hx_mem
    have hx_in : x ∈ f ⁻¹' {w.toWitness.value} :=
      (Set.Finite.mem_toFinset w.toWitness.fiber_finite).mp hx_mem
    exact manifoldRamificationIndex_eq_one_at_regularWitnessReg_preimage
      hf w hx_in
  -- Sum of 1s over a Finset = card.
  calc ∑ x ∈ w.toWitness.fiber_finite.toFinset, manifoldRamificationIndex f x
      = ∑ _x ∈ w.toWitness.fiber_finite.toFinset, 1 := by
        exact Finset.sum_congr rfl h_each
    _ = w.toWitness.fiber_finite.toFinset.card := by
        simp
    _ = w.card := rfl

/-- **Total ramification weight, packaged as a `Finset.sum`.**
Restatement of `sum_manifoldRamificationIndex_eq_card_of_regularWitnessReg`
making the `w.fiber_finite` defeq explicit. -/
theorem sum_manifoldRamificationIndex_fiber_eq_card_of_regularWitnessReg
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω f)
    (w : RegularValueWitnessReg f) :
    ∑ x ∈ w.fiber_finite.toFinset, manifoldRamificationIndex f x = w.card :=
  sum_manifoldRamificationIndex_eq_card_of_regularWitnessReg hf w

end Manifold
end JacobianChallenge

end

end
