/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.NearbyRegularValueExistsDischarge
import JacobianChallenge.Manifold.FibreDisjointChartRadiusDecomposition
import JacobianChallenge.Manifold.NearbyRegularWitnessDischarge
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional
import JacobianChallenge.Manifold.RamificationSumRegular
import Mathlib.Data.Set.Card.Arithmetic

set_option diagnostics.threshold 100
set_option maxHeartbeats 2000000

/-! # `NearbyRegularWitnessHypothesis X Y` — unconditional discharge -/

open scoped Manifold ContDiff
open Set Filter Topology Metric

noncomputable section

namespace JacobianChallenge

universe u v

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
variable (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]

theorem nearbyRegularWitnessHypothesis_holds_unconditional :
    JacobianChallenge.ContMDiff.Owed.degree.NearbyRegularWitnessHypothesis X Y := by
  intro f hf hnc y₀
  classical
  obtain ⟨hF_fin, eps, V_nbhd, hV_open, hy₀_V, _h_eps_pos, h_disj, h_preim, h_count⟩ :=
    JacobianChallenge.Manifold.fibre_disjoint_chart_radius_decomposition f hf hnc y₀
  obtain ⟨y', hy'_V, hy'_ne, hy'_reg⟩ :=
    nearbyRegularValueExists_holds_unconditional X Y f hf hnc y₀ V_nbhd hV_open hy₀_V
  -- The chart-disk index used by the decomposition output.
  let Dseq : X → Set X := fun x =>
    (chartAt ℂ x).source ∩
      (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
        (if h : x ∈ hF_fin.toFinset then eps x h else 0)
  -- f ⁻¹' {y'} ⊆ ⋃ x ∈ hF_fin.toFinset, Dseq x
  have h_subset : f ⁻¹' {y'} ⊆ ⋃ x ∈ hF_fin.toFinset, Dseq x := by
    intro z hz
    have hfz : f z = y' := hz
    have : z ∈ f ⁻¹' V_nbhd := by simp [hfz, hy'_V]
    exact h_preim this
  -- f ⁻¹' {y'} = ⋃ x ∈ hF_fin.toFinset, f ⁻¹' {y'} ∩ Dseq x
  have h_decomp :
      f ⁻¹' {y'} = ⋃ x ∈ hF_fin.toFinset, f ⁻¹' {y'} ∩ Dseq x := by
    apply Set.Subset.antisymm
    · intro z hz
      have hz_in_union := h_subset hz
      simp only [Set.mem_iUnion] at hz_in_union ⊢
      obtain ⟨x, hx, hzD⟩ := hz_in_union
      exact ⟨x, hx, hz, hzD⟩
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨_, _, hz_int⟩ := hz
      exact hz_int.1
  -- For each x ∈ hF_fin.toFinset: ncard of f ⁻¹' {y'} ∩ Dseq x = ramificationIndex
  have h_per_x_ncard : ∀ x ∈ hF_fin.toFinset,
      (f ⁻¹' {y'} ∩ Dseq x).ncard =
        JacobianChallenge.Manifold.manifoldRamificationIndex f x := by
    intro x hx
    have key := h_count y' hy'_V hy'_ne x hx
    -- Dseq x with the if-then-else reduces to (...) using hx.
    have h_dif : (if h : x ∈ hF_fin.toFinset then eps x h else 0) = eps x hx := by
      simp [hx]
    show (f ⁻¹' {y'} ∩ ((chartAt ℂ x).source ∩
      (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x)
        (if h : x ∈ hF_fin.toFinset then eps x h else 0))).ncard = _
    rw [h_dif]
    exact key
  -- Finiteness of each piece (ramificationIndex pos => ncard pos => finite + nonempty)
  have h_per_x_fin : ∀ x ∈ hF_fin.toFinset, (f ⁻¹' {y'} ∩ Dseq x).Finite := by
    intro x hx
    have hxy₀ : f x = y₀ := by
      have : x ∈ f ⁻¹' {y₀} := (Set.Finite.mem_toFinset hF_fin).mp hx
      exact this
    have h_ram_pos : 1 ≤ JacobianChallenge.Manifold.manifoldRamificationIndex f x :=
      JacobianChallenge.Manifold.manifoldRamificationIndex_pos_unconditional hf hnc hxy₀
    have h_ncard_pos : 0 < (f ⁻¹' {y'} ∩ Dseq x).ncard := by
      rw [h_per_x_ncard x hx]; exact h_ram_pos
    by_contra h_not_fin
    have h_inf : (f ⁻¹' {y'} ∩ Dseq x).Infinite := h_not_fin
    rw [h_inf.ncard] at h_ncard_pos
    exact lt_irrefl 0 h_ncard_pos
  -- Pairwise disjointness inherited.
  have h_disj_inter :
      (↑hF_fin.toFinset : Set X).PairwiseDisjoint
        (fun x => f ⁻¹' {y'} ∩ Dseq x) := by
    intro x hx y hy hxy
    have h_orig := h_disj hx hy hxy
    exact h_orig.mono Set.inter_subset_right Set.inter_subset_right
  -- f ⁻¹' {y'} is finite.
  have h_setFin : (↑hF_fin.toFinset : Set X).Finite := hF_fin.toFinset.finite_toSet
  have h_fib_fin : (f ⁻¹' {y'}).Finite := by
    rw [h_decomp]
    refine h_setFin.biUnion ?_
    intro x hx
    exact h_per_x_fin x hx
  -- ncard sum
  have h_ncard_sum :
      (f ⁻¹' {y'}).ncard =
        ∑ x ∈ hF_fin.toFinset, JacobianChallenge.Manifold.manifoldRamificationIndex f x := by
    rw [h_decomp]
    rw [show (⋃ x ∈ hF_fin.toFinset, f ⁻¹' {y'} ∩ Dseq x) =
            ⋃ x ∈ (↑hF_fin.toFinset : Set X), f ⁻¹' {y'} ∩ Dseq x from by ext; simp]
    rw [h_setFin.ncard_biUnion h_per_x_fin h_disj_inter]
    rw [finsum_mem_coe_finset]
    exact Finset.sum_congr rfl h_per_x_ncard
  -- Build the witness.
  let w_base : JacobianChallenge.ContMDiff.RegularValueWitness f :=
    { value := y', fiber_finite := h_fib_fin }
  refine ⟨w_base.toRegular hy'_reg, ?_⟩
  show h_fib_fin.toFinset.card = _
  rw [← Set.ncard_eq_toFinset_card _ h_fib_fin, h_ncard_sum]

end JacobianChallenge

end
