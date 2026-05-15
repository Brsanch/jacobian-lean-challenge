/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2PuncturedSimplyConnected

/-! # Two stereographic charts cover the standard 2-sphere

A small but useful building block for the Phase-3 smoothing arc
(discharging `S2LoopHomotopicToAvoidingLoop`, see
`Topology/S2LoopsNullHomotopicReduction.lean`).

Mathlib's `stereographic hv : OpenPartialHomeomorph (sphere 0 1) ((ℝ ∙ v)ᗮ)`
has `source = {⟨v, hv⟩}ᶜ` — the whole sphere minus the chosen
"north pole" `v`. Taking the antipodal chart (`-v` as north pole),
the two sources cover the sphere: their intersection is the
"equatorial" region `sphere ∖ {v, -v}`, and their union is everything.

This file packages that covering as:

* `norm_neg_one_of_norm_one` — `‖v‖ = 1 ⇒ ‖-v‖ = 1`.
* `northPole_ne_southPole` — `⟨v, hv⟩ ≠ ⟨-v, _⟩` on the unit sphere.
* `stereographic_source_union_neg_eq_univ` —
  `(stereographic hv).source ∪ (stereographic _).source = univ`,
  where the second chart uses `-v` as its north pole.
* `exists_stereographic_chart_containing` — for every
  `p : sphere 0 1`, either `p ∈ (stereographic hv).source` or
  `p ∈ (stereographic h_neg).source`.

Downstream use: in the Lebesgue-number polygonal-approximation step
the two-chart cover is the smallest finite open cover of `S²` by
stereographic chart sources; it keeps the case analysis to two
branches.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

variable {v : EuclideanSpace ℝ (Fin 3)}

/-- If `‖v‖ = 1` then `‖-v‖ = 1`. -/
theorem norm_neg_one_of_norm_one (hv : ‖v‖ = 1) :
    ‖(-v : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  simp [hv]

/-- A unit vector is not its own negation: `v = -v` would give
`2 • v = 0`, hence `v = 0` (since `(2 : ℝ) ≠ 0`), contradicting
`‖v‖ = 1`. -/
theorem ne_neg_self_of_norm_one (hv : ‖v‖ = 1) : v ≠ -v := by
  intro h_eq
  have h_two : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h_eq]
    exact add_neg_cancel v
  have h_v_zero : v = 0 :=
    (smul_eq_zero.mp h_two).resolve_left (by norm_num)
  have h_norm_zero : ‖v‖ = 0 := by rw [h_v_zero]; exact norm_zero
  rw [h_norm_zero] at hv
  exact one_ne_zero hv.symm

/-- On the unit sphere, the "north pole" `⟨v, _⟩` and "south pole"
`⟨-v, _⟩` are distinct subtype elements. Direct corollary of
`ne_neg_self_of_norm_one`. -/
theorem northPole_ne_southPole (hv : ‖v‖ = 1) :
    (⟨v, by simp [hv]⟩ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≠
      ⟨-v, by simp [hv]⟩ := by
  intro h
  apply ne_neg_self_of_norm_one hv
  simpa [Subtype.ext_iff] using h

/-! ## Two-chart cover -/

/-- For every `p : sphere 0 1`, at least one of the two stereographic
charts (at `v` or at `-v`) contains `p` in its source. Case-split on
`p = ⟨v, _⟩`: if yes, `p` is in the south chart's source (since the
south pole `⟨-v, _⟩` is distinct from `⟨v, _⟩`); if no, `p` is in the
north chart's source directly. -/
theorem exists_stereographic_chart_containing
    (hv : ‖v‖ = 1) (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    p ∈ (stereographic hv).source ∨
      p ∈ (stereographic (norm_neg_one_of_norm_one hv)).source := by
  rw [stereographic_source hv, stereographic_source (norm_neg_one_of_norm_one hv)]
  by_cases h : p = (⟨v, by simp [hv]⟩ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  · -- `p` is the north pole; it lives in the south chart's source.
    right
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h_south
    have h_pole_eq :
        (⟨v, by simp [hv]⟩ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =
          ⟨-v, by simp [norm_neg_one_of_norm_one hv]⟩ :=
      h.symm.trans h_south
    exact northPole_ne_southPole hv h_pole_eq
  · -- `p ≠ north pole`; it lives in the north chart's source.
    left
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact h

/-- The union of the stereographic chart at `v` and the stereographic
chart at `-v` covers the entire unit sphere. Direct corollary of
`exists_stereographic_chart_containing`. -/
theorem stereographic_source_union_neg_eq_univ (hv : ‖v‖ = 1) :
    (stereographic hv).source ∪
        (stereographic (norm_neg_one_of_norm_one hv)).source =
      (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  refine Set.eq_univ_of_forall (fun p => ?_)
  exact exists_stereographic_chart_containing hv p

end JacobianChallenge

end
