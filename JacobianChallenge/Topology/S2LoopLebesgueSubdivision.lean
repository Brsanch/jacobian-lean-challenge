/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2TwoChartCover
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Lebesgue subdivision for the two-chart cover of `S²`

Building block for the Phase-3 smoothing arc. Combines mathlib's
`lebesgue_number_lemma` with the two-chart cover from
`Topology/S2TwoChartCover.lean` to produce, for every continuous loop
parameter `f : C(unitInterval, sphere 0 1)`, a uniform `δ > 0` such
that any δ-ball in `[0,1]` maps under `f` into a single stereographic
chart's source.

The δ is the Lebesgue number of the open cover `{f⁻¹U, f⁻¹V}` of
`unitInterval`, where `U = (stereographic hv).source` and
`V = (stereographic h_neg).source`. Compactness of `unitInterval`
makes the lemma applicable.

This is one half of the subdivision step in the polygonal-approximation
argument; the other half (turning δ into a finite partition of `[0,1]`
with explicit endpoints) and the polygonal construction itself remain
for subsequent chips.

## What is proved

* `JacobianChallenge.exists_lebesgue_radius_for_two_chart_cover` —
  for every continuous `f : C(unitInterval, sphere 0 1)` and every
  unit vector `v ∈ EuclideanSpace ℝ (Fin 3)`, there is `δ > 0` such
  that for every `x : unitInterval`, the `δ`-ball around `x` is
  contained in either `f⁻¹(stereographic hv).source` or
  `f⁻¹(stereographic (norm_neg_one_of_norm_one hv)).source`.

  Equivalently: for any pair of points `s, t ∈ unitInterval` with
  `dist s t < δ`, `f s` and `f t` both lie in the source of a common
  stereographic chart (the same chart for both).

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set Filter Topology

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)

/-- The two preimages, under a continuous `f : C(unitInterval, sphere 0 1)`,
of the two stereographic chart sources form an open cover of
`unitInterval`. -/
theorem two_chart_preimage_cover_unitInterval
    (f : C(unitInterval, sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    (Set.univ : Set unitInterval) ⊆
      f ⁻¹' (stereographic hv).source ∪
        f ⁻¹' (stereographic (norm_neg_one_of_norm_one hv)).source := by
  intro x _
  rcases exists_stereographic_chart_containing hv (f x) with h₁ | h₂
  · exact Or.inl h₁
  · exact Or.inr h₂

/-- **Lebesgue radius for the two-chart cover.** For every continuous
`f : C(unitInterval, sphere 0 1)` and unit vector `v`, there exists
`δ > 0` such that for every `x : unitInterval`,
`Metric.ball x δ ⊆ f ⁻¹' (stereographic hv).source` or
`Metric.ball x δ ⊆ f ⁻¹' (stereographic _).source`.

Proof: apply `lebesgue_number_lemma` to the open cover of `unitInterval`
by the two pullbacks (open since `f` is continuous and the chart sources
are open). Convert the entourage to a metric `δ > 0` via
`Metric.mem_uniformity_dist`. -/
theorem exists_lebesgue_radius_for_two_chart_cover
    (f : C(unitInterval, sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    ∃ δ > 0, ∀ x : unitInterval,
      Metric.ball x δ ⊆ f ⁻¹' (stereographic hv).source ∨
        Metric.ball x δ ⊆
          f ⁻¹' (stereographic (norm_neg_one_of_norm_one hv)).source := by
  -- Two-element open cover of unitInterval.
  let U : Fin 2 → Set unitInterval := fun i =>
    if i = 0 then f ⁻¹' (stereographic hv).source
    else f ⁻¹' (stereographic (norm_neg_one_of_norm_one hv)).source
  have hopen : ∀ i, IsOpen (U i) := by
    intro i
    fin_cases i
    · simp only [U]; exact (stereographic hv).open_source.preimage f.continuous
    · simp only [U]
      exact ((stereographic (norm_neg_one_of_norm_one hv)).open_source).preimage f.continuous
  have hcover : (Set.univ : Set unitInterval) ⊆ ⋃ i, U i := by
    intro x _
    rcases exists_stereographic_chart_containing hv (f x) with h₁ | h₂
    · exact mem_iUnion.mpr ⟨0, by simp only [U]; simpa⟩
    · exact mem_iUnion.mpr ⟨1, by simp only [U]; simpa⟩
  -- Compact unitInterval ⇒ Lebesgue number lemma applies.
  obtain ⟨V, hV_uni, hV_ball⟩ :=
    lebesgue_number_lemma isCompact_univ hopen hcover
  -- Convert the entourage V to a metric δ.
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_uniformity_dist.mp hV_uni
  refine ⟨δ, hδ_pos, fun x => ?_⟩
  obtain ⟨i, hi⟩ := hV_ball x (Set.mem_univ _)
  have h_ball_sub : Metric.ball x δ ⊆ UniformSpace.ball x V := by
    intro y hy
    have h_dist : dist x y < δ := by
      rw [Metric.mem_ball] at hy
      rwa [dist_comm]
    have h_pair : (x, y) ∈ V := hδ_sub h_dist
    exact h_pair
  have h_sub_Ui : Metric.ball x δ ⊆ U i := h_ball_sub.trans hi
  -- Case-split on i.
  fin_cases i
  · exact Or.inl (by simpa only [U] using h_sub_Ui)
  · exact Or.inr (by simpa only [U] using h_sub_Ui)

end JacobianChallenge

end
