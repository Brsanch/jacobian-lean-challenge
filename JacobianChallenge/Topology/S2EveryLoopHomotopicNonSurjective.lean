/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2PartitionVertices
import JacobianChallenge.Topology.S2SingleChartLoopNonSurjective
import JacobianChallenge.Topology.S2LoopAvoidingFromNonSurjective
import Mathlib.Topology.Subpath
import Mathlib.Topology.Closure

/-! # Discharge of `EveryS2LoopHomotopicToNonSurjective`

The final assembly chip. Combines all of chips 1–4i'' into the
headline theorem closing the Phase-3 smoothing gap.

No `sorry`, no `axiom`.
-/

noncomputable section

open Metric Set

namespace JacobianChallenge

/-! ## Cast helper for Path.Homotopy across endpoint types -/

/-- Transport a `Path.Homotopy` across propositional endpoint equalities.
The underlying continuous function is unchanged; only the endpoint types
in the paths' indices are relabeled. -/
private def homotopyRecastEndpoints
    {X : Type*} [TopologicalSpace X]
    {a b a' b' : X} {p q : Path a b}
    (H : Path.Homotopy p q) (ha : a' = a) (hb : b' = b) :
    Path.Homotopy (p.cast ha hb) (q.cast ha hb) where
  toFun := H.toFun
  continuous_toFun := H.continuous_toFun
  map_zero_left x := H.map_zero_left x
  map_one_left x := H.map_one_left x
  prop' t x hx := H.prop' t x hx

/-- Transport `Path.Homotopic` across propositional endpoint equalities. -/
private theorem homotopicRecastEndpoints
    {X : Type*} [TopologicalSpace X]
    {a b a' b' : X} {p q : Path a b}
    (h : Path.Homotopic p q) (ha : a' = a) (hb : b' = b) :
    Path.Homotopic (p.cast ha hb) (q.cast ha hb) :=
  ⟨homotopyRecastEndpoints h.some ha hb⟩

/-! ## Chart-vector extraction -/

private theorem chart_eq_to_unitVec
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    (C : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hC : C = (stereographic hv).source ∨
              C = (stereographic (norm_neg_one_of_norm_one hv)).source) :
    ∃ (w : EuclideanSpace ℝ (Fin 3)) (hw : ‖w‖ = 1),
      C = (stereographic hw).source := by
  rcases hC with hN | hS
  · exact ⟨v, hv, hN⟩
  · exact ⟨-v, norm_neg_one_of_norm_one hv, hS⟩

/-! ## Subpath image membership -/

private theorem subpath_image_in_chart
    {N : ℕ} (hN_pos : 0 < N)
    {x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (γ : Path x x)
    (chart : Fin N → Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (h_chart_mem :
      ∀ (k : Fin N) (s : unitInterval),
        ((k : ℝ) / N) ≤ (s : ℝ) → (s : ℝ) ≤ ((k : ℝ) + 1) / N →
          γ.toContinuousMap s ∈ chart k)
    (k : Fin N) (r : unitInterval) :
    γ.subpath (partitionVertex N hN_pos k.castSucc)
        (partitionVertex N hN_pos k.succ) r ∈ chart k := by
  show γ _ ∈ chart k
  have h_le : (partitionVertex N hN_pos k.castSucc : unitInterval) ≤
      partitionVertex N hN_pos k.succ := by
    rw [← Subtype.coe_le_coe]
    rw [partitionVertex_castSucc_val N hN_pos k,
        partitionVertex_succ_val N hN_pos k]
    have : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    exact div_le_div_of_nonneg_right this (by exact_mod_cast hN_pos.le)
  have hs_lo := Icc.le_convexCombo h_le r
  rw [← Subtype.coe_le_coe, partitionVertex_castSucc_val N hN_pos k] at hs_lo
  have hs_hi := Icc.convexCombo_le h_le r
  rw [← Subtype.coe_le_coe, partitionVertex_succ_val N hN_pos k] at hs_hi
  exact h_chart_mem k _ hs_lo hs_hi

/-! ## Range concat -/

private theorem range_concat_subset_refl_union_iUnion
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (p : Fin (N + 1) → X)
    (F : (k : Fin N) → Path (p k.castSucc) (p k.succ)) :
    Set.range (Path.concat p F : Path (p 0) (p (Fin.last N))) ⊆
      Set.range (Path.refl (p 0)) ∪ ⋃ k : Fin N, Set.range (F k) := by
  induction N with
  | zero =>
    rw [Path.concat_zero]
    intro y hy
    exact Or.inl hy
  | succ n ih =>
    rw [Path.concat_succ]
    intro y hy
    have h_trans_eq := Path.trans_range
      (Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc))
      (F (Fin.last n))
    have hy' :
        y ∈ Set.range ⇑(Path.concat (p ∘ Fin.castSucc) (fun k => F k.castSucc)) ∪
            Set.range ⇑(F (Fin.last n)) := h_trans_eq ▸ hy
    rcases hy' with hy | hy
    · have := ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) hy
      rcases this with hy_refl | hy_union
      · exact Or.inl hy_refl
      · refine Or.inr ?_
        rcases Set.mem_iUnion.mp hy_union with ⟨k, hk⟩
        exact Set.mem_iUnion.mpr ⟨k.castSucc, hk⟩
    · refine Or.inr ?_
      exact Set.mem_iUnion.mpr ⟨Fin.last n, hy⟩

private theorem range_concat_subset_iUnion_of_pos
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (p : Fin (N + 1) → X) (F : (k : Fin N) → Path (p k.castSucc) (p k.succ))
    (hN_pos : 0 < N) :
    Set.range (Path.concat p F : Path (p 0) (p (Fin.last N))) ⊆
      ⋃ k : Fin N, Set.range (F k) := by
  set k0 : Fin N := ⟨0, hN_pos⟩
  have h_k0_castSucc : (k0.castSucc : Fin (N + 1)) = 0 := by
    apply Fin.ext
    rfl
  intro y hy
  have h_loose := range_concat_subset_refl_union_iUnion p F hy
  rcases h_loose with h_refl | h_union
  · obtain ⟨_, hy_eq⟩ := h_refl
    refine Set.mem_iUnion.mpr ⟨k0, 0, ?_⟩
    have h_source : F k0 0 = p k0.castSucc := (F k0).source
    rw [h_source, h_k0_castSucc]
    exact hy_eq
  · exact h_union

/-! ## Closed nowhere-dense union -/

private theorem range_stereographicStraightLine_isClosed
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ = 1)
    {p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hp : p ∈ (stereographic hv).source)
    (hq : q ∈ (stereographic hv).source) :
    IsClosed (Set.range (stereographicStraightLine hv p q hp hq)) :=
  (isCompact_range (stereographicStraightLine hv p q hp hq).continuous).isClosed

private theorem interior_iUnion_closed_empty
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (S : Fin N → Set X)
    (hS_closed : ∀ k, IsClosed (S k))
    (hS_int : ∀ k, interior (S k) = ∅) :
    interior (⋃ k : Fin N, S k) = ∅ := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h_union :
        (⋃ k : Fin (n + 1), S k) =
          (⋃ k : Fin n, S k.castSucc) ∪ S (Fin.last n) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_union]
      refine ⟨?_, ?_⟩
      · rintro ⟨k, hk⟩
        rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
        · exact Or.inl ⟨j, hk⟩
        · exact Or.inr hk
      · rintro (⟨k, hk⟩ | hk)
        · exact ⟨k.castSucc, hk⟩
        · exact ⟨Fin.last n, hk⟩
    rw [h_union]
    have h_left_closed : IsClosed (⋃ k : Fin n, S k.castSucc) :=
      isClosed_iUnion_of_finite (fun k => hS_closed _)
    have h_left_int : interior (⋃ k : Fin n, S k.castSucc) = ∅ :=
      ih (fun k => S k.castSucc) (fun k => hS_closed _) (fun k => hS_int _)
    rw [interior_union_isClosed_of_interior_empty h_left_closed (hS_int _)]
    exact h_left_int

private theorem standardS2_univ_nonempty :
    (Set.univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).Nonempty := by
  have hne : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    refine ⟨⟨EuclideanSpace.single 0 (1 : ℝ), ?_⟩⟩
    simp [mem_sphere_iff_norm]
  exact ⟨hne.some, Set.mem_univ _⟩

/-! ## Path equality: γ.cast = γ.subpath (pV 0) (pV last) -/

private theorem γCast_eq_subpath
    {N : ℕ} (hN_pos : 0 < N)
    {x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (γ : Path x x)
    (h_source : (γ ∘ partitionVertex N hN_pos) 0 = x)
    (h_target : (γ ∘ partitionVertex N hN_pos) (Fin.last N) = x) :
    γ.cast h_source h_target =
      γ.subpath (partitionVertex N hN_pos 0)
        (partitionVertex N hN_pos (Fin.last N)) := by
  apply DFunLike.coe_injective
  funext s
  -- LHS = γ.cast applied at s = γ s (cast preserves toFun)
  -- RHS = γ.subpath ... applied at s = γ (Icc.convexCombo ... s)
  show γ s = γ (Icc.convexCombo (partitionVertex N hN_pos 0)
    (partitionVertex N hN_pos (Fin.last N)) s)
  congr 1
  apply Subtype.ext
  rw [Icc.coe_convexCombo,
      show (partitionVertex N hN_pos 0 : unitInterval) = 0 from
        partitionVertex_zero N hN_pos,
      show (partitionVertex N hN_pos (Fin.last N) : unitInterval) = 1 from
        partitionVertex_last N hN_pos]
  show (s : ℝ) = (1 - (s : ℝ)) * ((0 : unitInterval) : ℝ) + (s : ℝ) * ((1 : unitInterval) : ℝ)
  show (s : ℝ) = (1 - (s : ℝ)) * 0 + (s : ℝ) * 1
  ring

/-! ## Final theorem -/

/-- **Every loop in `StandardS2` is path-homotopic to a non-surjective loop.** -/
theorem everyS2LoopHomotopicToNonSurjective_holds :
    EveryS2LoopHomotopicToNonSurjective := by
  intro x γ
  classical
  -- Step 1: chip 4c with v = e_0.
  set v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ) with hv_def
  have hv : ‖v‖ = 1 := by simp [hv_def]
  obtain ⟨N, hN_pos, chart, h_chart_choice, h_chart_mem⟩ :=
    exists_chart_indexed_partition γ.toContinuousMap hv
  have h_choose := fun k => chart_eq_to_unitVec hv (chart k) (h_chart_choice k)
  choose chartVec chartHv h_chart_eq using h_choose
  -- Step 2: endpoint memberships.
  have h_endpoint_castSucc : ∀ k : Fin N,
      γ (partitionVertex N hN_pos k.castSucc) ∈
        (stereographic (chartHv k)).source := by
    intro k
    have h_lo : ((k : ℝ) / N) ≤
        ((partitionVertex N hN_pos k.castSucc : unitInterval) : ℝ) := by
      rw [partitionVertex_castSucc_val N hN_pos k]
    have h_hi : ((partitionVertex N hN_pos k.castSucc : unitInterval) : ℝ) ≤
        ((k : ℝ) + 1) / N := by
      rw [partitionVertex_castSucc_val N hN_pos k]
      exact div_le_div_of_nonneg_right (by linarith) (by exact_mod_cast hN_pos.le)
    have := h_chart_mem k _ h_lo h_hi
    rwa [h_chart_eq k] at this
  have h_endpoint_succ : ∀ k : Fin N,
      γ (partitionVertex N hN_pos k.succ) ∈
        (stereographic (chartHv k)).source := by
    intro k
    have h_lo : ((k : ℝ) / N) ≤
        ((partitionVertex N hN_pos k.succ : unitInterval) : ℝ) := by
      rw [partitionVertex_succ_val N hN_pos k]
      exact div_le_div_of_nonneg_right (by linarith) (by exact_mod_cast hN_pos.le)
    have h_hi : ((partitionVertex N hN_pos k.succ : unitInterval) : ℝ) ≤
        ((k : ℝ) + 1) / N := by
      rw [partitionVertex_succ_val N hN_pos k]
    have := h_chart_mem k _ h_lo h_hi
    rwa [h_chart_eq k] at this
  -- Step 3: per-piece straight lines.
  set straightLine : (k : Fin N) →
      Path
        ((γ ∘ partitionVertex N hN_pos) k.castSucc)
        ((γ ∘ partitionVertex N hN_pos) k.succ) :=
    fun k => stereographicStraightLine (chartHv k)
      ((γ ∘ partitionVertex N hN_pos) k.castSucc)
      ((γ ∘ partitionVertex N hN_pos) k.succ)
      (h_endpoint_castSucc k) (h_endpoint_succ k) with hstraight_def
  set γ_concat :=
    Path.concat (γ ∘ partitionVertex N hN_pos) straightLine with hγ_concat_def
  have h_concat_source : (γ ∘ partitionVertex N hN_pos) 0 = x := by
    show γ (partitionVertex N hN_pos 0) = x
    rw [partitionVertex_zero N hN_pos]; exact γ.source
  have h_concat_target : (γ ∘ partitionVertex N hN_pos) (Fin.last N) = x := by
    show γ (partitionVertex N hN_pos (Fin.last N)) = x
    rw [partitionVertex_last N hN_pos]; exact γ.target
  set γ' : Path x x :=
    γ_concat.cast h_concat_source.symm h_concat_target.symm with hγ'_def
  refine ⟨γ', ?_, ?_⟩
  · -- Homotopy γ ≃ γ'.
    -- Build the homotopy at type Path ((γ ∘ pV) 0) ((γ ∘ pV) (last)) and then
    -- recast endpoints back to Path x x.
    -- Chain: γ.cast h_source h_target = γ.subpath (pV 0) (pV (last))
    --      ≃ Path.concat (γ ∘ pV) (γ.subpath k.castSucc k.succ)  [concat_subpath.symm]
    --      ≃ Path.concat (γ ∘ pV) straightLine = γ_concat        [concat_hcomp]
    have h_piecewise_hom : ∀ k : Fin N,
        Path.Homotopic
          (γ.subpath (partitionVertex N hN_pos k.castSucc)
            (partitionVertex N hN_pos k.succ))
          (straightLine k) := by
      intro k
      apply stereographicStraightLine_homotopic
      intro r
      have h_in_chart := subpath_image_in_chart hN_pos γ chart h_chart_mem k r
      rwa [h_chart_eq k] at h_in_chart
    have h_concat_hcomp :
        Path.Homotopic
          (Path.concat (γ ∘ partitionVertex N hN_pos)
            (fun k => γ.subpath (partitionVertex N hN_pos k.castSucc)
              (partitionVertex N hN_pos k.succ)))
          γ_concat :=
      Path.Homotopic.concat_hcomp (γ ∘ partitionVertex N hN_pos) _ _ h_piecewise_hom
    have h_subpath_concat :
        Path.Homotopic
          (Path.concat (γ ∘ partitionVertex N hN_pos)
            (fun k => γ.subpath (partitionVertex N hN_pos k.castSucc)
              (partitionVertex N hN_pos k.succ)))
          (γ.subpath (partitionVertex N hN_pos 0)
            (partitionVertex N hN_pos (Fin.last N))) :=
      Path.Homotopic.concat_subpath γ (partitionVertex N hN_pos)
    have h_cast_eq_subpath := γCast_eq_subpath hN_pos γ h_concat_source h_concat_target
    have h_chain_typed :
        Path.Homotopic (γ.cast h_concat_source h_concat_target) γ_concat := by
      rw [h_cast_eq_subpath]
      exact h_subpath_concat.symm.trans h_concat_hcomp
    -- Recast both sides' endpoints back to Path x x.
    -- γ.cast h_concat_source h_concat_target at type Path ((γ ∘ pV) 0) ((γ ∘ pV) (last)).
    -- Recast with hx = h_concat_source.symm (x = (γ ∘ pV) 0) and hy = h_concat_target.symm.
    -- Result: (γ.cast).cast (back) = γ (definitionally? or via Path.ext).
    --        γ_concat.cast (back) = γ' (by definition).
    have h_chain_recast :
        Path.Homotopic
          ((γ.cast h_concat_source h_concat_target).cast
            h_concat_source.symm h_concat_target.symm) γ' :=
      homotopicRecastEndpoints h_chain_typed h_concat_source.symm h_concat_target.symm
    -- (γ.cast h_concat_source h_concat_target).cast h_concat_source.symm h_concat_target.symm = γ
    -- as paths at type Path x x, by Path.ext (same toFun = γ.toFun).
    have h_double_cast_eq_γ :
        (γ.cast h_concat_source h_concat_target).cast
          h_concat_source.symm h_concat_target.symm = γ := by
      ext s
      rfl
    rw [h_double_cast_eq_γ] at h_chain_recast
    exact h_chain_recast
  · -- range γ' ≠ univ.
    intro h_range_univ
    have h_range_γ' : Set.range γ' = Set.range γ_concat := by
      ext z
      refine ⟨?_, ?_⟩
      · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht]; rfl⟩
      · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht]; rfl⟩
    rw [h_range_γ'] at h_range_univ
    have h_range_sub :
        Set.range γ_concat ⊆ ⋃ k : Fin N, Set.range (straightLine k) :=
      range_concat_subset_iUnion_of_pos
        (γ ∘ partitionVertex N hN_pos) straightLine hN_pos
    have hS_closed : ∀ k : Fin N, IsClosed (Set.range (straightLine k)) :=
      fun k => range_stereographicStraightLine_isClosed (chartHv k)
        (h_endpoint_castSucc k) (h_endpoint_succ k)
    have hS_int : ∀ k : Fin N, interior (Set.range (straightLine k)) = ∅ :=
      fun k => interior_range_stereographicStraightLine_eq_empty (chartHv k)
        (h_endpoint_castSucc k) (h_endpoint_succ k)
    have h_union_int :
        interior (⋃ k : Fin N, Set.range (straightLine k)) = ∅ :=
      interior_iUnion_closed_empty _ hS_closed hS_int
    have h_interior_concat :
        interior (Set.range γ_concat) ⊆
          interior (⋃ k : Fin N, Set.range (straightLine k)) :=
      interior_mono h_range_sub
    rw [h_union_int] at h_interior_concat
    have h_int_empty : interior (Set.range γ_concat) = ∅ :=
      Set.subset_empty_iff.mp h_interior_concat
    rw [h_range_univ, interior_univ] at h_int_empty
    exact standardS2_univ_nonempty.ne_empty h_int_empty

end JacobianChallenge

end
