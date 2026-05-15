/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2TwoChartCover
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # The "equatorial belt" `S² ∖ {v, -v}` is path-connected

A building block for the Phase-3 smoothing arc: any continuous loop
in `StandardS2` can be deformed inside each chart so its global image
sits in the **equatorial belt** `S² ∖ {v, -v}` for a suitable choice
of unit vector `v` missing the (finite) set of partition vertices.
For that strategy the belt must be path-connected so the in-chart
replacement paths exist with the original endpoints.

The argument runs via the stereographic homeomorphism. With `v` a
unit vector in `EuclideanSpace ℝ (Fin 3)`:

* The orthogonal complement `(ℝ ∙ v)ᗮ` is 2-dimensional over `ℝ`
  (mathlib: `Submodule.finrank_orthogonal_span_singleton` with
  `finrank_euclideanSpace_fin`).
* `(ℝ ∙ v)ᗮ ∖ {0}` is path-connected — direct application of
  `isPathConnected_compl_singleton_of_one_lt_rank` to the
  two-dimensional Euclidean inner product space.
* Mathlib's `stereographic_apply_neg` maps `⟨-v, _⟩ : sphere 0 1` to
  `0 ∈ (ℝ ∙ v)ᗮ`. Combined with the homeomorphism
  `S2Punctured v hv ≃ₜ (ℝ ∙ v)ᗮ` (chip 2's
  `S2Punctured.stereographicHomeomorph`), the preimage of `{0}` is
  exactly the south-pole point of the punctured sphere.
* Transport path-connectedness through the homeomorphism.

## What is proved

* `JacobianChallenge.finrank_orthogonalComplement_v_eq_two` — for any
  unit vector `v ∈ EuclideanSpace ℝ (Fin 3)`,
  `Module.finrank ℝ (ℝ ∙ v)ᗮ = 2`.
* `JacobianChallenge.rank_orthogonalComplement_v_gt_one` — corollary
  for `Module.rank`.
* `JacobianChallenge.isPathConnected_orthogonalComplement_compl_zero`
  — `(ℝ ∙ v)ᗮ ∖ {0}` is path-connected.
* `JacobianChallenge.isPathConnected_S2_minus_two_poles` — the
  equatorial belt `S² ∖ {⟨v, _⟩, ⟨-v, _⟩}` is path-connected as a
  `Set (sphere 0 1)`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

/-! ## Rank facts about `(ℝ ∙ v)ᗮ` -/

/-- The orthogonal complement of `ℝ ∙ v` in `EuclideanSpace ℝ (Fin 3)`
has `ℝ`-finrank `2`, for any nonzero `v`. -/
theorem finrank_orthogonalComplement_v_eq_two
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    Module.finrank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) = 2 := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton
    (show v ≠ 0 by
      intro h
      rw [h, norm_zero] at hv
      exact one_ne_zero hv.symm)

/-- The orthogonal complement has `Module.rank` strictly greater than `1`
— prerequisite for `isPathConnected_compl_singleton_of_one_lt_rank`. -/
theorem rank_orthogonalComplement_v_gt_one
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    (1 : Cardinal) <
      Module.rank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) := by
  rw [← Module.finrank_eq_rank, finrank_orthogonalComplement_v_eq_two hv]
  exact_mod_cast (by norm_num : (1 : ℕ) < 2)

/-! ## Path-connectedness in `(ℝ ∙ v)ᗮ` -/

/-- The complement of `{0}` in `(ℝ ∙ v)ᗮ` is path-connected. Direct
application of `isPathConnected_compl_singleton_of_one_lt_rank`. -/
theorem isPathConnected_orthogonalComplement_compl_zero
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    IsPathConnected
      (({0} : Set ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))))ᶜ) :=
  isPathConnected_compl_singleton_of_one_lt_rank
    (rank_orthogonalComplement_v_gt_one hv) 0

/-! ## The equatorial belt of `S²` -/

/-- The two-pole set `{⟨v, _⟩, ⟨-v, _⟩}` in `sphere 0 1`. -/
def twoPoleSet {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  {(⟨v, by simp [hv]⟩ : sphere _ _), ⟨-v, by simp [hv]⟩}

/-- The "equatorial belt" `S² ∖ {v, -v}`. -/
def equatorialBelt {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  (twoPoleSet hv)ᶜ

/-- A point `p : sphere 0 1` is in the equatorial belt iff its underlying
vector is neither `v` nor `-v`. -/
theorem mem_equatorialBelt_iff
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    p ∈ equatorialBelt hv ↔
      p ≠ (⟨v, by simp [hv]⟩ : sphere _ _) ∧
        p ≠ (⟨-v, by simp [hv]⟩ : sphere _ _) := by
  simp [equatorialBelt, twoPoleSet, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]

/-- The equatorial belt is contained in the north stereographic chart's
source. -/
theorem equatorialBelt_subset_northSource
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    equatorialBelt hv ⊆ (stereographic hv).source := by
  intro p hp
  rw [stereographic_source]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ((mem_equatorialBelt_iff hv p).mp hp).1

/-- The equatorial belt is contained in the south stereographic chart's
source. -/
theorem equatorialBelt_subset_southSource
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    equatorialBelt hv ⊆ (stereographic (norm_neg_one_of_norm_one hv)).source := by
  intro p hp
  rw [stereographic_source]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ((mem_equatorialBelt_iff hv p).mp hp).2

/-! ## Path-connectedness of the equatorial belt -/

/-- The stereographic image of the equatorial belt is the complement of
`{0}` in `(ℝ ∙ v)ᗮ`. -/
theorem stereographic_symm_image_compl_zero_eq_equatorialBelt
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    ((stereographic hv).symm : (ℝ ∙ v)ᗮ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ''
        (({0} : Set ((ℝ ∙ v)ᗮ : Submodule ℝ _))ᶜ) =
      equatorialBelt hv := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx_ne_zero, hx_eq⟩
    -- p = (stereographic hv).symm x with x ≠ 0.
    -- Show p ∈ equatorialBelt = sphere ∖ {⟨v, _⟩, ⟨-v, _⟩}.
    -- First, p ∈ (stereographic hv).source via symm_image_target_eq_source.
    have h_target_x : x ∈ (stereographic hv).target := by
      rw [stereographic_target hv]; exact Set.mem_univ _
    have h_p_in_source : p ∈ (stereographic hv).source := by
      rw [← hx_eq]; exact (stereographic hv).map_target h_target_x
    have h_p_ne_north : p ≠ (⟨v, by simp [hv]⟩ : sphere _ _) := by
      intro h_eq
      rw [stereographic_source hv, h_eq] at h_p_in_source
      simp at h_p_in_source
    have h_p_ne_south : p ≠ (⟨-v, by simp [hv]⟩ : sphere _ _) := by
      intro h_eq
      -- If p = ⟨-v, _⟩, then stereographic hv p = 0, but stereographic hv p = x ≠ 0.
      have h_stereo_p : (stereographic hv) p = x := by
        rw [← hx_eq, (stereographic hv).right_inv h_target_x]
      have h_stereo_neg : (stereographic hv) p =
          (stereographic hv) (⟨-v, by simp [hv]⟩ : sphere _ _) := by rw [h_eq]
      have h_zero : (stereographic hv) (⟨-v, by simp [hv]⟩ : sphere _ _) = 0 :=
        stereographic_apply_neg ⟨v, by simp [hv]⟩
      rw [h_zero] at h_stereo_neg
      rw [h_stereo_neg] at h_stereo_p
      exact hx_ne_zero h_stereo_p.symm
    exact (mem_equatorialBelt_iff hv p).mpr ⟨h_p_ne_north, h_p_ne_south⟩
  · intro hp
    -- p ∈ equatorialBelt ⇒ exists x ≠ 0 with (stereographic hv).symm x = p.
    have h_p_in_source : p ∈ (stereographic hv).source :=
      equatorialBelt_subset_northSource hv hp
    refine ⟨(stereographic hv) p, ?_, ?_⟩
    · -- x = stereographic p ≠ 0. If x = 0, then p = (stereographic hv).symm 0 = ⟨-v, _⟩.
      intro h_eq
      have h_south : (stereographic hv) (⟨-v, by simp [hv]⟩ : sphere _ _) = 0 :=
        stereographic_apply_neg ⟨v, by simp [hv]⟩
      have h_inj : Set.InjOn (stereographic hv) (stereographic hv).source :=
        (stereographic hv).injOn
      have h_neg_in_source :
          (⟨-v, by simp [hv]⟩ : sphere _ _) ∈ (stereographic hv).source := by
        rw [stereographic_source]
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h_v_eq_neg_v
        exact ne_neg_self_of_norm_one hv (by
          have := congrArg Subtype.val h_v_eq_neg_v
          simpa using this.symm)
      have h_p_eq_neg : p = (⟨-v, by simp [hv]⟩ : sphere _ _) :=
        h_inj h_p_in_source h_neg_in_source (h_eq.trans h_south.symm)
      exact ((mem_equatorialBelt_iff hv p).mp hp).2 h_p_eq_neg
    · exact (stereographic hv).left_inv h_p_in_source

/-- **The equatorial belt is path-connected.** Image of the
path-connected `(ℝ ∙ v)ᗮ ∖ {0}` under the continuous map
`(stereographic hv).symm`. -/
theorem isPathConnected_equatorialBelt
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1) :
    IsPathConnected (equatorialBelt hv) := by
  rw [← stereographic_symm_image_compl_zero_eq_equatorialBelt hv]
  refine (isPathConnected_orthogonalComplement_compl_zero hv).image' ?_
  -- `(stereographic hv).symm` is continuous on its source, which equals
  -- `(stereographic hv).target = univ`. Hence continuous on `{0}ᶜ`.
  have h_cont_on_target :
      ContinuousOn ((stereographic hv).symm) (stereographic hv).target :=
    (stereographic hv).continuousOn_symm
  rw [stereographic_target hv] at h_cont_on_target
  exact h_cont_on_target.mono (Set.subset_univ _)

end JacobianChallenge

end
