/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalKFoldGenuineManifoldCount
import JacobianChallenge.Manifold.NearbyRegularWitnessDischarge
import JacobianChallenge.Manifold.RamificationSumComposer
import JacobianChallenge.Manifold.RamificationSumEqualsDegreeUnconditional
import JacobianChallenge.Manifold.RegularValueExistsRegUnconditional
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.RamificationIndexPositive
import JacobianChallenge.Manifold.PerChartNonConstancyReduction
import JacobianChallenge.Manifold.ChartOverlapPropagationDischarge
import JacobianChallenge.Manifold.ClopennessOfLocallyConstDischarge
import JacobianChallenge.Manifold.CriticalValuesFiniteGeneral
import JacobianChallenge.Manifold.FibresFiniteUnconditional
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import JacobianChallenge.Manifold.AnalyticKthRoot
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.PreimageEventualContainment
import JacobianChallenge.Manifold.DisjointFibreNbhds

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional discharge of `NearbyRegularWitnessHypothesis`

This file (the **RH-NRW-v2** chip) discharges
`NearbyRegularWitnessHypothesis X Y` unconditionally, using
`localKFoldMultiplicityOnManifold_genuine_preimage_card` (the chip
`ManifoldKFold`) at the heart together with topological assembly
(disjoint fibre nbhds in T2, preimage eventual containment, and the
unconditional finiteness of the critical-value set).

## Strategy

For non-constant analytic `f : X → Y` and `y : Y`, the fibre
`F := f ⁻¹' {y}` is finite (by `fibres_finite_statement_holds_unconditional`).
For each `x ∈ F`, the ramification index `k_x` is at least `1` (via
`manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy`).

We supply a per-`x` chart-disk `D_x` of radius `ε_x`, where `ε_x` is
chosen small enough that `D_x` is contained in a pairwise-disjoint open
neighbourhood `W_x` of `x` (delivered by `Set.Finite.t2_separation` via
`exists_disjoint_open_nbhds_of_finite`). The genuine manifold-level
fibre count needs the radius to be supplied as input; we therefore
re-prove a radius-bounded variant inline (a near-verbatim copy of
`localKFoldMultiplicityOnManifold_genuine_preimage_card`'s proof, with
an additional user-supplied radius bound `R₀`).

With pairwise-disjoint `D_x ⊆ W_x`, `preimage_eventually_in_fibre_neighbourhoods`
delivers an open `V₀ ∋ y` with `f ⁻¹' V₀ ⊆ ⋃ x ∈ F, D_x`. Removing
`(criticalValuesGeneral f) ∪ {y}` (a finite set) from
`V₀ ∩ ⋂ x ∈ F, V_x` leaves a non-empty open set (since `Y` is infinite
and the critical-value set is finite). Pick `w` in that set:

* `w` is a regular value, so `f ⁻¹' {w}` is finite and at every
  preimage the chart-pullback derivative is non-zero (witness
  certificate);
* the disjointness of `D_x` partitions `f ⁻¹' {w}` along `x ∈ F`, with
  `(f ⁻¹' {w} ∩ D_x).ncard = k_x` from the per-`x` count;
* therefore `|f ⁻¹' {w}| = ∑ x ∈ F, k_x`.

This is exactly the conclusion `NearbyRegularWitnessHypothesis X Y`
demands.

## What this file ships

* `localKFoldMultiplicityOnManifold_genuine_with_radius` — the radius-
  bounded variant of the genuine manifold-level fibre count, copied
  inline (no signature change to the existing headline theorem).
* `nearbyRegularWitnessHypothesis_holds_unconditional` — the
  unconditional discharge of the analytic input named by
  `RamificationSumComposer.lean`.
* `ramificationSumEqualsDegree_holds_unconditional` — the named
  obligation `Owed.degree.ramificationSumEqualsDegree_statement X Y`,
  composed via `ramificationSumEqualsDegree_holds_of_nearby_regular_witness_only`.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Function
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace Manifold

universe u v

/-! ## Inlined radius-bounded planar `k`-fold count -/

/-- **`k = 1` planar count with a radius bound (re-derivation).**

Counts preimages of values near `g x₀` in a metric ball of radius
`ε ≤ R`. -/
private theorem localOneFold_preimage_card_with_radius_bound_aux
    {g : ℂ → ℂ} {x₀ : ℂ}
    (h_an : AnalyticAt ℂ g x₀) (hd : deriv g x₀ ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    ∃ ε > (0 : ℝ), ε ≤ R ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = 1 := by
  have hsd : HasStrictDerivAt g (deriv g x₀) x₀ := h_an.hasStrictDerivAt
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g x₀) hd) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv hd
  set φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g with hφ
  have h_x0_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_w0_tgt : g x₀ ∈ φ.target := hsfd.image_mem_toOpenPartialHomeomorph_target
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds h_x0_src
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.mem_nhds_iff.mp h_src_nhds
  set ε : ℝ := min ε₀ R with hε_def
  have hε_pos : 0 < ε := lt_min hε₀_pos hR
  have hε_le_R : ε ≤ R := min_le_right _ _
  have hε_le_ε₀ : ε ≤ ε₀ := min_le_left _ _
  have hε_sub : Metric.ball x₀ ε ⊆ φ.source := fun z hz =>
    hε₀_sub (Metric.ball_subset_ball hε_le_ε₀ hz)
  have h_symm_cont : ContinuousAt φ.symm (g x₀) :=
    (φ.continuousOn_symm).continuousAt (φ.open_target.mem_nhds h_w0_tgt)
  have h_symm_w0 : φ.symm (g x₀) = x₀ := by
    have hpre := φ.left_inv h_x0_src
    have hφx₀ : (φ : ℂ → ℂ) x₀ = g x₀ := by rw [h_coe]
    rw [hφx₀] at hpre
    exact hpre
  have h_ball_x0_nhds : Metric.ball x₀ ε ∈ 𝓝 x₀ :=
    Metric.ball_mem_nhds x₀ hε_pos
  have h_preimage_nhds : φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) := by
    have ht := h_symm_cont.tendsto
    rw [h_symm_w0] at ht
    exact ht h_ball_x0_nhds
  have h_combo_nhds :
      φ.target ∩ φ.symm ⁻¹' (Metric.ball x₀ ε) ∈ 𝓝 (g x₀) :=
    Filter.inter_mem (φ.open_target.mem_nhds h_w0_tgt) h_preimage_nhds
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
  refine ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw_target : w ∈ φ.target := (hδ_sub hw_ball).1
  have hw_pre_in_ball : φ.symm w ∈ Metric.ball x₀ ε := (hδ_sub hw_ball).2
  have h_symm_w_src : φ.symm w ∈ φ.source := φ.map_target hw_target
  have h_g_symm : g (φ.symm w) = w := by
    have hr : (φ : ℂ → ℂ) (φ.symm w) = w := φ.right_inv hw_target
    rw [h_coe] at hr
    exact hr
  have h_preimage_eq :
      {z ∈ Metric.ball x₀ ε | g z = w} = {φ.symm w} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨hw_pre_in_ball, h_g_symm⟩, ?_⟩
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_src : z ∈ φ.source := hε_sub hz_ball
    have hφz : (φ : ℂ → ℂ) z = w := by rw [h_coe]; exact hz_g
    have hφ_symm_w : (φ : ℂ → ℂ) (φ.symm w) = w := by
      rw [h_coe]; exact h_g_symm
    exact φ.injOn hz_src h_symm_w_src (hφz.trans hφ_symm_w.symm)
  rw [h_preimage_eq]
  exact Set.ncard_singleton _

/-- **Planar `k`-fold count with `ε ≤ R` (re-derivation).** -/
private theorem localKFoldMultiplicity_preimage_card_with_radius_bound_aux
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R : ℝ}
    (hk : 1 ≤ k) (hR : 0 < R)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ ε > (0 : ℝ), ε ≤ R ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  obtain ⟨R₀, hR₀_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  set R' : ℝ := min R₀ R with hR'_def
  have hR'_pos : 0 < R' := lt_min hR₀_pos hR
  have hR'_le_R₀ : R' ≤ R₀ := min_le_left _ _
  have hR'_le_R : R' ≤ R := min_le_right _ _
  have hu_an' : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R') :=
    fun z hz => hu_an z (Metric.closedBall_subset_closedBall hR'_le_R₀ hz)
  have hfact' : ∀ z ∈ Metric.closedBall x₀ R',
      g z - w₀ = (z - x₀) ^ k * u z :=
    fun z hz => hfact z (Metric.closedBall_subset_closedBall hR'_le_R₀ hz)
  obtain ⟨r, ρ_v, hρ_v_pos, hρ_v_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR'_pos hu_an' hu_x₀ hk
  set v_actual : ℂ → ℂ := fun z => (z - x₀) * r z with hvact_def
  have hva_an : AnalyticOnNhd ℂ v_actual (Metric.closedBall x₀ ρ_v) := by
    intro z hz
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      analyticAt_id.sub analyticAt_const
    have h2 : AnalyticAt ℂ r z := hr_an z hz
    exact h1.mul h2
  have hva_x₀ : v_actual x₀ = 0 := by
    show (x₀ - x₀) * r x₀ = 0
    simp
  have hva_d : deriv v_actual x₀ ≠ 0 := by
    have hx₀_in : x₀ ∈ Metric.closedBall x₀ ρ_v := Metric.mem_closedBall_self hρ_v_pos.le
    have hr_x₀_pow : r x₀ ^ k = u x₀ := hr_pow x₀ hx₀_in
    have hr_x₀_ne : r x₀ ≠ 0 := by
      intro h
      have hpow : (0 : ℂ) ^ k = u x₀ := by rw [← h]; exact hr_x₀_pow
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      rw [zero_pow hk0] at hpow
      exact hu_x₀ hpow.symm
    have hr_diff : DifferentiableAt ℂ r x₀ := (hr_an x₀ hx₀_in).differentiableAt
    have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
      (differentiableAt_id).sub (differentiableAt_const x₀)
    have hderiv :
        deriv v_actual x₀ =
          deriv (fun ζ : ℂ => ζ - x₀) x₀ * r x₀ +
          (x₀ - x₀) * deriv r x₀ := by
      simpa [hvact_def] using deriv_mul hsub_diff hr_diff
    have hderiv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have hh : deriv (fun ζ : ℂ => ζ - x₀) x₀
            = deriv (id : ℂ → ℂ) x₀ - deriv (fun _ : ℂ => x₀) x₀ :=
        deriv_sub differentiableAt_id (differentiableAt_const x₀)
      rw [hh]; simp
    rw [hderiv, hderiv_sub, sub_self, zero_mul, add_zero, one_mul]
    exact hr_x₀_ne
  have hva_pow : ∀ z ∈ Metric.closedBall x₀ ρ_v, g z - w₀ = v_actual z ^ k := by
    intro z hz
    have hz_R' : z ∈ Metric.closedBall x₀ R' :=
      (Metric.closedBall_subset_closedBall hρ_v_le) hz
    have h1 : g z - w₀ = (z - x₀) ^ k * u z := hfact' z hz_R'
    have h2 : r z ^ k = u z := hr_pow z hz
    show g z - w₀ = ((z - x₀) * r z) ^ k
    rw [h1, ← h2, mul_pow]
  have hva_at_x₀ : AnalyticAt ℂ v_actual x₀ :=
    hva_an x₀ (Metric.mem_closedBall_self hρ_v_pos.le)
  obtain ⟨ε, hε_pos, hε_le_ρv, δ₁, hδ₁_pos, hZZ74_v⟩ :=
    localOneFold_preimage_card_with_radius_bound_aux hva_at_x₀ hva_d hρ_v_pos
  have hε_le_R : ε ≤ R := hε_le_ρv.trans (hρ_v_le.trans hR'_le_R)
  rw [show v_actual x₀ = 0 from hva_x₀] at hZZ74_v
  set δ : ℝ := (δ₁ / 2) ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos (by linarith) k
  refine ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  have hw₀_eq_gx₀ : w₀ = g x₀ := h_w₀.symm
  set w₁ : ℂ := w - w₀ with hw₁_def
  have hw₁_ne : w₁ ≠ 0 := by
    rw [hw₁_def, sub_ne_zero, hw₀_eq_gx₀]; exact hw_ne
  have hw_dist : ‖w - w₀‖ < δ := by
    have hh : ‖w - g x₀‖ < δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hw_ball; exact hw_ball
    rw [hw₀_eq_gx₀]; exact hh
  have h_roots_small : ∀ ξ : ℂ, ξ ^ k = w₁ → ‖ξ‖ < δ₁ := by
    intro ξ hξ
    have hξn : ‖ξ‖ ^ k = ‖w₁‖ := by rw [← norm_pow, hξ]
    have h1 : ‖ξ‖ ^ k < (δ₁ / 2) ^ k := by
      rw [hξn, ← hδ_def]; exact hw_dist
    have hδ₁_half_nn : 0 ≤ δ₁ / 2 := by linarith
    have h2 : ‖ξ‖ < δ₁ / 2 := by
      by_contra h
      push_neg at h
      have hh : (δ₁ / 2) ^ k ≤ ‖ξ‖ ^ k := pow_le_pow_left₀ hδ₁_half_nn h k
      linarith
    linarith
  have h_roots_ne : ∀ ξ : ℂ, ξ ^ k = w₁ → ξ ≠ 0 := by
    intro ξ hξ hξ0
    rw [hξ0] at hξ
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    rw [zero_pow hk0] at hξ
    exact hw₁_ne hξ.symm
  classical
  set Pre : Set ℂ := {z ∈ Metric.ball x₀ ε | g z = w} with hPre_def
  set Fset : Finset ℂ :=
    (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).roots.toFinset with hFset_def
  have hp_ne : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ) ≠ 0 := by
    intro hh
    have hdeg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
      Polynomial.natDegree_X_pow_sub_C
    rw [hh] at hdeg
    simp at hdeg
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    exact hk0 hdeg.symm
  have hFset_iff : ∀ ξ : ℂ, ξ ∈ Fset ↔ ξ ^ k = w₁ := by
    intro ξ
    rw [hFset_def, Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
    constructor
    · intro hroot
      unfold Polynomial.IsRoot at hroot
      simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero] at hroot
      exact hroot
    · intro hpow
      unfold Polynomial.IsRoot
      simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero, hpow]
  have h_ball_sub_closed : Metric.ball x₀ ε ⊆ Metric.closedBall x₀ ρ_v := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    exact (le_of_lt hz).trans hε_le_ρv
  have h_v_to_roots : ∀ z ∈ Pre, v_actual z ∈ Fset := by
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_closed : z ∈ Metric.closedBall x₀ ρ_v := h_ball_sub_closed hz_ball
    have hpow : g z - w₀ = v_actual z ^ k := hva_pow z hz_closed
    rw [hz_g] at hpow
    have hvk : v_actual z ^ k = w₁ := by rw [hw₁_def]; exact hpow.symm
    exact (hFset_iff (v_actual z)).mpr hvk
  have h_v_count : ∀ ξ ∈ Fset, ({z ∈ Metric.ball x₀ ε | v_actual z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξ
    have hξk : ξ ^ k = w₁ := (hFset_iff ξ).mp hξ
    have hξ_ne : ξ ≠ 0 := h_roots_ne ξ hξk
    have hξ_norm : ‖ξ‖ < δ₁ := h_roots_small ξ hξk
    have hξ_ball : ξ ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hξ_norm
    exact hZZ74_v ξ hξ_ball hξ_ne
  have h_exists : ∀ ξ ∈ Fset, ∃ z ∈ Pre, v_actual z = ξ := by
    intro ξ hξ
    have h_card1 := h_v_count ξ hξ
    have h_finite : ({z ∈ Metric.ball x₀ ε | v_actual z = ξ} : Set ℂ).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [h_card1]; exact one_ne_zero)
    have h_ne : ({z ∈ Metric.ball x₀ ε | v_actual z = ξ} : Set ℂ).Nonempty := by
      rw [← Set.ncard_pos h_finite, h_card1]; exact Nat.one_pos
    obtain ⟨z, hz_ball_mem, hzv⟩ := h_ne
    refine ⟨z, ⟨hz_ball_mem, ?_⟩, hzv⟩
    have hz_closed : z ∈ Metric.closedBall x₀ ρ_v := h_ball_sub_closed hz_ball_mem
    have hpow : g z - w₀ = v_actual z ^ k := hva_pow z hz_closed
    rw [hzv] at hpow
    have hξk : ξ ^ k = w₁ := (hFset_iff ξ).mp hξ
    rw [hξk] at hpow
    have : g z = w₁ + w₀ := by
      have hh : g z = (g z - w₀) + w₀ := by ring
      rw [hh, hpow]
    rw [this, hw₁_def]; ring
  have h_v_injOn : Set.InjOn v_actual Pre := by
    intro z₁ hz₁ z₂ hz₂ hvz
    have hξ : v_actual z₁ ∈ Fset := h_v_to_roots z₁ hz₁
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v_actual z = v_actual z₁} : Set ℂ).ncard = 1 :=
      h_v_count (v_actual z₁) hξ
    have hz₁_mem : z₁ ∈ ({z ∈ Metric.ball x₀ ε | v_actual z = v_actual z₁} : Set ℂ) :=
      ⟨hz₁.1, rfl⟩
    have hz₂_mem : z₂ ∈ ({z ∈ Metric.ball x₀ ε | v_actual z = v_actual z₁} : Set ℂ) :=
      ⟨hz₂.1, hvz.symm⟩
    rw [Set.ncard_eq_one] at h_card1
    obtain ⟨a, ha⟩ := h_card1
    rw [ha] at hz₁_mem hz₂_mem
    rw [Set.mem_singleton_iff] at hz₁_mem hz₂_mem
    exact hz₁_mem.trans hz₂_mem.symm
  have h_image_eq : v_actual '' Pre = (Fset : Set ℂ) := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨z, hz_pre, hzy⟩ := hy
      rw [← hzy]
      exact_mod_cast h_v_to_roots z hz_pre
    · intro ξ hξ
      have hξF : ξ ∈ Fset := by exact_mod_cast hξ
      obtain ⟨z, hz_pre, hzv⟩ := h_exists ξ hξF
      exact ⟨z, hz_pre, hzv⟩
  have hF_card : Fset.card = k := by
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    have hp_deg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
      Polynomial.natDegree_X_pow_sub_C
    have h_separable : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).Separable :=
      Polynomial.separable_X_pow_sub_C w₁ (by exact_mod_cast hk0) hw₁_ne
    have h_splits : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).Splits :=
      IsAlgClosed.splits _
    have h_card_roots : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).roots.card =
        (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree :=
      Polynomial.splits_iff_card_roots.mp h_splits
    have h_nodup : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).roots.Nodup :=
      Polynomial.nodup_roots h_separable
    rw [hFset_def, Multiset.toFinset_card_of_nodup h_nodup, h_card_roots, hp_deg]
  have hPre_ncard : Pre.ncard = Fset.card := by
    have h1 : Pre.ncard = (v_actual '' Pre).ncard :=
      (Set.InjOn.ncard_image h_v_injOn).symm
    rw [h1, h_image_eq, Set.ncard_coe_finset]
  rw [hPre_ncard, hF_card]

/-! ## Radius-bounded genuine manifold-level fibre count -/

/-- **Genuine manifold-level fibre count, with a user-supplied radius bound.**

For real-analytic `f : X → Y` and a fibre point `x` with positive
ramification index, plus an additional radius bound `R₀ > 0`, there
exist `ε ≤ R₀` and an open neighbourhood `V ∋ f x` such that for every
`w ∈ V \ {f x}`, the count
`(f ⁻¹' {w} ∩ D_x).ncard = manifoldRamificationIndex f x`,
where `D_x = (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' (ball ((chartAt ℂ x) x) ε)`.

This is the radius-bounded variant of
`localKFoldMultiplicityOnManifold_genuine_preimage_card`; the only
addition is the user-supplied bound `R₀` on the output `ε`. -/
theorem localKFoldMultiplicityOnManifold_genuine_with_radius
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X)
    (hpos : 1 ≤ manifoldRamificationIndex f x)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ (ε : ℝ) (V : Set Y), 0 < ε ∧ ε ≤ R₀ ∧ IsOpen V ∧ f x ∈ V ∧
      (∀ w ∈ V, w ≠ f x →
        (f ⁻¹' {w} ∩
          ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
          = manifoldRamificationIndex f x) := by
  classical
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set k : ℕ := manifoldRamificationIndex f x with hk_def
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  have hF_z₀_eq : F z₀ = (chartAt ℂ (f x)) (f x) := by
    have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (chartAt ℂ (f x)) (f x)
    simp [Function.comp, (chartAt ℂ x).left_inv hx_src]
  have hord : analyticOrderAt (fun z => F z - F z₀) z₀ = (k : ℕ∞) := by
    have hk_eq : k = (analyticOrderAt (fun z => F z - F z₀) z₀).toNat := rfl
    have hk_toNat : 1 ≤ (analyticOrderAt (fun z => F z - F z₀) z₀).toNat := by
      rw [hk_eq] at hpos; exact hpos
    have hord_ne_top : analyticOrderAt (fun z => F z - F z₀) z₀ ≠ ⊤ := by
      intro h
      rw [h, ENat.toNat_top] at hk_toNat
      exact absurd hk_toNat (by norm_num)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hord_ne_top
    have hk_n : k = n := by rw [hk_eq, ← hn, ENat.toNat_coe]
    rw [← hn, hk_n]
  have h_target_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
  have hz₀_target : z₀ ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have h_target_nhds : (chartAt ℂ x).target ∈ 𝓝 z₀ :=
    h_target_open.mem_nhds hz₀_target
  obtain ⟨R_t, hR_t_pos, hR_t_sub⟩ := Metric.mem_nhds_iff.mp h_target_nhds
  have h_f_cont : Continuous f := hf.continuous
  have h_open_x : IsOpen ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) :=
    (chartAt ℂ x).open_source.inter ((chartAt ℂ (f x)).open_source.preimage h_f_cont)
  have h_x_mem : x ∈ (chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source :=
    ⟨mem_chart_source ℂ x, mem_chart_source ℂ (f x)⟩
  have h_symm_cont : ContinuousAt (chartAt ℂ x).symm z₀ := by
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt h_target_nhds
  have h_symm_z₀ : (chartAt ℂ x).symm z₀ = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_pre_nhds :
      (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) ∈ 𝓝 z₀ := by
    have ht := h_symm_cont.tendsto
    rw [h_symm_z₀] at ht
    exact ht (h_open_x.mem_nhds h_x_mem)
  have h_combined :
      (chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) ∈ 𝓝 z₀ :=
    Filter.inter_mem h_target_nhds h_pre_nhds
  obtain ⟨R_c, hR_c_pos, hR_c_sub⟩ := Metric.mem_nhds_iff.mp h_combined
  set R : ℝ := min (min R_t R_c) R₀ with hR_def
  have hR_pos : 0 < R := lt_min (lt_min hR_t_pos hR_c_pos) hR₀
  have hR_le_R_t : R ≤ R_t := (min_le_left _ _).trans (min_le_left _ _)
  have hR_le_R_c : R ≤ R_c := (min_le_left _ _).trans (min_le_right _ _)
  have hR_le_R₀ : R ≤ R₀ := min_le_right _ _
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, h_count⟩ :=
    localKFoldMultiplicity_preimage_card_with_radius_bound_aux (g := F) (x₀ := z₀)
      (w₀ := F z₀) (k := k) (R := R) hpos hR_pos hF_an rfl hord
  have hε_le_R_t : ε ≤ R_t := hε_le_R.trans hR_le_R_t
  have hε_le_R_c : ε ≤ R_c := hε_le_R.trans hR_le_R_c
  have hε_le_R₀ : ε ≤ R₀ := hε_le_R.trans hR_le_R₀
  set V : Set Y := (chartAt ℂ (f x)).source ∩
    (chartAt ℂ (f x)) ⁻¹' Metric.ball (F z₀) δ with hV_def
  have h_V_open : IsOpen V := by
    have hco : ContinuousOn (chartAt ℂ (f x)) (chartAt ℂ (f x)).source :=
      (chartAt ℂ (f x)).continuousOn_toFun
    have hball_open : IsOpen (Metric.ball (F z₀) δ) := Metric.isOpen_ball
    exact hco.isOpen_inter_preimage (chartAt ℂ (f x)).open_source hball_open
  have h_fx_in_V : f x ∈ V := by
    refine ⟨mem_chart_source ℂ (f x), ?_⟩
    show (chartAt ℂ (f x)) (f x) ∈ Metric.ball (F z₀) δ
    rw [hF_z₀_eq]; exact Metric.mem_ball_self hδ_pos
  refine ⟨ε, V, hε_pos, hε_le_R₀, h_V_open, h_fx_in_V, ?_⟩
  intro w hw_V hw_ne
  obtain ⟨hw_src, hw_ball⟩ := hw_V
  set c : ℂ := (chartAt ℂ (f x)) w with hc_def
  have hc_ball : c ∈ Metric.ball (F z₀) δ := hw_ball
  have hc_ne : c ≠ F z₀ := by
    rw [hc_def, hF_z₀_eq]
    intro hc_eq
    exact hw_ne ((chartAt ℂ (f x)).injOn hw_src (mem_chart_source ℂ (f x)) hc_eq)
  have h_planar_count : ({z ∈ Metric.ball z₀ ε | F z = c} : Set ℂ).ncard = k :=
    h_count c hc_ball hc_ne
  set Planar : Set ℂ := {z ∈ Metric.ball z₀ ε | F z = c} with hPlanar_def
  set D_x : Set X := (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball z₀ ε with hD_def
  set Manifold' : Set X := f ⁻¹' {w} ∩ D_x with hMan_def
  have h_ball_sub_target : Metric.ball z₀ ε ⊆ (chartAt ℂ x).target := fun z hz =>
    hR_t_sub (Metric.ball_subset_ball hε_le_R_t hz)
  have h_ball_sub_combined :
      Metric.ball z₀ ε ⊆
        (chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) :=
    fun z hz => hR_c_sub (Metric.ball_subset_ball hε_le_R_c hz)
  have h_forward : (chartAt ℂ x).symm '' Planar ⊆ Manifold' := by
    rintro x' ⟨z, hz_planar, hz_eq⟩
    obtain ⟨hz_ball, hz_F⟩ := hz_planar
    have hz_target : z ∈ (chartAt ℂ x).target := h_ball_sub_target hz_ball
    have hz_combined := h_ball_sub_combined hz_ball
    have hz_symm_in : (chartAt ℂ x).symm z ∈
        (chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source := hz_combined.2
    have hx'_src : x' ∈ (chartAt ℂ x).source := by rw [← hz_eq]; exact hz_symm_in.1
    have hf_x'_src : f x' ∈ (chartAt ℂ (f x)).source := by
      rw [← hz_eq]; exact hz_symm_in.2
    have hx'_chart : (chartAt ℂ x) x' = z := by
      rw [← hz_eq]; exact (chartAt ℂ x).right_inv hz_target
    have h_F_z : F z = (chartAt ℂ (f x)) (f x') := by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = (chartAt ℂ (f x)) (f x')
      simp [Function.comp, hz_eq]
    have hfx'_eq : f x' = w := by
      have h1 : (chartAt ℂ (f x)) (f x') = (chartAt ℂ (f x)) w := by
        rw [← h_F_z, hz_F]
      exact (chartAt ℂ (f x)).injOn hf_x'_src hw_src h1
    refine ⟨?_, ?_⟩
    · show f x' ∈ ({w} : Set Y); exact hfx'_eq
    refine ⟨hx'_src, ?_⟩
    show (chartAt ℂ x) x' ∈ Metric.ball z₀ ε
    rw [hx'_chart]; exact hz_ball
  have h_backward : Manifold' ⊆ (chartAt ℂ x).symm '' Planar := by
    rintro x' ⟨hfx', hD⟩
    obtain ⟨hx'_src, hx'_chart_ball⟩ := hD
    have hfx'_w : f x' = w := hfx'
    set z : ℂ := (chartAt ℂ x) x' with hz_def
    have hz_ball : z ∈ Metric.ball z₀ ε := hx'_chart_ball
    have hz_symm : (chartAt ℂ x).symm z = x' := (chartAt ℂ x).left_inv hx'_src
    have h_F_z : F z = (chartAt ℂ (f x)) (f x') := by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = (chartAt ℂ (f x)) (f x')
      simp [Function.comp, hz_symm]
    have h_F_z_eq_c : F z = c := by rw [h_F_z, hfx'_w, hc_def]
    refine ⟨z, ⟨hz_ball, h_F_z_eq_c⟩, hz_symm⟩
  have h_set_eq : Manifold' = (chartAt ℂ x).symm '' Planar :=
    Set.Subset.antisymm h_backward h_forward
  have h_injOn : Set.InjOn (chartAt ℂ x).symm Planar := by
    intro a ha b hb hab
    have ha_target : a ∈ (chartAt ℂ x).target := h_ball_sub_target ha.1
    have hb_target : b ∈ (chartAt ℂ x).target := h_ball_sub_target hb.1
    have ha_eq : (chartAt ℂ x) ((chartAt ℂ x).symm a) = a := (chartAt ℂ x).right_inv ha_target
    have hb_eq : (chartAt ℂ x) ((chartAt ℂ x).symm b) = b := (chartAt ℂ x).right_inv hb_target
    rw [hab] at ha_eq
    exact ha_eq.symm.trans hb_eq
  have h_ncard : Manifold'.ncard = Planar.ncard := by
    rw [h_set_eq]
    exact Set.InjOn.ncard_image h_injOn
  rw [h_ncard, h_planar_count]

/-! ## Auxiliary: regular witness from `y ∉ criticalValuesGeneral f` -/

/-- For `y ∉ criticalValuesGeneral f`, every preimage `x ∈ f ⁻¹' {y}`
satisfies the chart-pullback-derivative-nonzero certificate. Re-uses the
private helper of `RegularValueExistsRegUnconditional.lean` via the
inline proof structure (we re-derive locally rather than depending on
that file's private namespace). -/
private lemma deriv_chart_pullback_ne_zero_at_regular_preimage
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y]
    {f : X → Y} (hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f)
    (hnc : ¬ JacobianChallenge.IsConstantMap f)
    {y : Y} (hy : y ∉ criticalValuesGeneral f)
    {x : X} (hx : x ∈ f ⁻¹' {y}) :
    deriv ((chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0 := by
  classical
  -- y ∉ criticalValuesGeneral f ⇒ x ∉ criticalSetGeneral f.
  have hfx_eq : f x = y := hx
  have hx_not_crit : x ∉ criticalSetGeneral f := by
    intro hx_crit
    apply hy
    exact ⟨x, hx_crit, hfx_eq⟩
  -- Hence f is locally injective at x.
  have h_inj : ∃ U ∈ 𝓝 x, Set.InjOn f U := by
    by_contra h
    apply hx_not_crit
    show ¬ ∃ U ∈ 𝓝 x, Set.InjOn f U
    exact h
  -- Set up F = (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm at c x.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f x ∈ d.source := mem_chart_source ℂ (f x)
  have hFA_at_x : AnalyticAt ℂ F (c x) :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- Non-eventual-constancy.
  have hClop :
      JacobianChallenge.ContMDiff.Owed.degree.ClopennessOfLocallyConstHypothesis X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      JacobianChallenge.ContMDiff.Owed.degree.ChartPullbackNotEventuallyConstHypothesis X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x) :=
    hChartNEC f hf hnc (f x) x rfl
  have hFcx : F (c x) = d (f x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f ∘ c.symm) (c x) = d (f x)
    simp [Function.comp, h_inv]
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f x)) (f x)
      have : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = F z from rfl,
          this, hFcx])
  -- Lift local injectivity of f at x to local injectivity of F at c x.
  have h_inj_F : ∃ U' ∈ 𝓝 (c x), Set.InjOn F U' := by
    obtain ⟨U, hU_nhds, hU_inj⟩ := h_inj
    set U₁ : Set X := U ∩ c.source ∩ f ⁻¹' d.source with hU₁_def
    have hf_cont : Continuous f := hf.continuous
    have hU₁_nhds : U₁ ∈ 𝓝 x :=
      Filter.inter_mem (Filter.inter_mem hU_nhds (c.open_source.mem_nhds hxc))
        (hf_cont.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hfx_d))
    have hU₁_subc : U₁ ⊆ c.source := fun _ hy' => hy'.1.2
    obtain ⟨U₁_open, hU₁_open_open, hU₁_open_sub, hx_U₁_open⟩ :
        ∃ U_o, IsOpen U_o ∧ U_o ⊆ U₁ ∧ x ∈ U_o := by
      obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
      exact ⟨W, hW_open, hW_sub, hxW⟩
    have hU₁_open_subc : U₁_open ⊆ c.source := hU₁_open_sub.trans hU₁_subc
    set U' : Set ℂ := c '' U₁_open with hU'_def
    have hU'_open : IsOpen U' :=
      c.isOpen_image_of_subset_source hU₁_open_open hU₁_open_subc
    have hcx_in_U' : c x ∈ U' := ⟨x, hx_U₁_open, rfl⟩
    have hU'_nhds : U' ∈ 𝓝 (c x) := hU'_open.mem_nhds hcx_in_U'
    refine ⟨U', hU'_nhds, ?_⟩
    rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF_eq
    have hy₁_subc : y₁ ∈ c.source := hU₁_open_subc hy₁_U
    have hy₂_subc : y₂ ∈ c.source := hU₁_open_subc hy₂_U
    have hy₁_U₁ : y₁ ∈ U₁ := hU₁_open_sub hy₁_U
    have hy₂_U₁ : y₂ ∈ U₁ := hU₁_open_sub hy₂_U
    have hy₁_U_outer : y₁ ∈ U := hy₁_U₁.1.1
    have hy₂_U_outer : y₂ ∈ U := hy₂_U₁.1.1
    have hy₁_fd : f y₁ ∈ d.source := hy₁_U₁.2
    have hy₂_fd : f y₂ ∈ d.source := hy₂_U₁.2
    have h_inv_y₁ : c.symm (c y₁) = y₁ := c.left_inv hy₁_subc
    have h_inv_y₂ : c.symm (c y₂) = y₂ := c.left_inv hy₂_subc
    have hF_at_y₁ : F (c y₁) = d (f y₁) := by
      show (d ∘ f ∘ c.symm) (c y₁) = d (f y₁)
      simp [Function.comp, h_inv_y₁]
    have hF_at_y₂ : F (c y₂) = d (f y₂) := by
      show (d ∘ f ∘ c.symm) (c y₂) = d (f y₂)
      simp [Function.comp, h_inv_y₂]
    rw [← hy₁_eq, ← hy₂_eq] at hF_eq
    rw [hF_at_y₁, hF_at_y₂] at hF_eq
    have h_inj_d : Set.InjOn d d.source := d.injOn
    have hf_eq : f y₁ = f y₂ := h_inj_d hy₁_fd hy₂_fd hF_eq
    have hy_eq : y₁ = y₂ := hU_inj hy₁_U_outer hy₂_U_outer hf_eq
    rw [← hy₁_eq, ← hy₂_eq, hy_eq]
  have hFA_sub : AnalyticAt ℂ (fun z => F z - F (c x)) (c x) :=
    hFA_at_x.sub analyticAt_const
  have h_ord_ne_top :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ ⊤ := by
    intro h_top
    apply hFne
    have h := analyticOrderAt_eq_top.mp h_top
    exact h.mono (fun z hz => sub_eq_zero.mp hz)
  have hF_self : (fun z => F z - F (c x)) (c x) = 0 := by simp
  have h_ord_ne_zero :
      analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ 0 := by
    intro h_zero
    have hne := (hFA_sub.analyticOrderAt_eq_zero).mp h_zero
    exact hne hF_self
  set ord : ℕ∞ := analyticOrderAt (fun z => F z - F (c x)) (c x) with hord_def
  obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, ord = (k : ℕ∞) := by
    cases hord_eq : ord with
    | top => exact absurd hord_eq h_ord_ne_top
    | coe n => exact ⟨n, by simp [hord_eq]⟩
  have hk_ge_one : 1 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k
    apply h_ord_ne_zero
    exact hk_eq
  have h_planar :
      (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) ↔ deriv F (c x) = 0 :=
    JacobianChallenge.Manifold.notInjOn_iff_deriv_zero_of_analytic_of_order
      hFA_at_x hk_ge_one hk_eq
  have h_neg_iff : ¬ (¬ ∃ U ∈ 𝓝 (c x), Set.InjOn F U) := by
    intro h_neg; exact h_neg h_inj_F
  -- Conclude deriv F (c x) ≠ 0; rewrite from f x to y.
  have h_d_fx : deriv F (c x) ≠ 0 := by
    by_contra h_d_zero
    exact h_neg_iff (h_planar.mpr h_d_zero)
  show deriv ((chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0
  rw [← hfx_eq]
  exact h_d_fx

/-! ## Y is infinite (re-derived locally)

We re-derive `Infinite Y` for compact connected complex 1-manifolds,
mirroring `RegularValueExistsRegUnconditional.y_infinite_of_chartedSpace_complex`. -/

private lemma neBot_nhdsNE_complex_local (z : ℂ) : Filter.NeBot (𝓝[≠] z) :=
  Module.punctured_nhds_neBot ℂ ℂ z

private lemma isOpen_complex_set_infinite_of_mem_local
    {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) : U.Infinite := by
  haveI : Filter.NeBot (𝓝[≠] z) := neBot_nhdsNE_complex_local z
  exact infinite_of_mem_nhds z (hU.mem_nhds hz)

private lemma y_infinite_of_chartedSpace_complex_local
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] : Infinite Y := by
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  set c : OpenPartialHomeomorph Y ℂ := chartAt ℂ y₀ with hc_def
  have hy₀_src : y₀ ∈ c.source := mem_chart_source ℂ y₀
  have hcy₀_tgt : c y₀ ∈ c.target := c.map_source hy₀_src
  have h_tgt_open : IsOpen c.target := c.open_target
  have h_tgt_inf : c.target.Infinite :=
    isOpen_complex_set_infinite_of_mem_local h_tgt_open hcy₀_tgt
  have h_inj_symm : Set.InjOn c.symm c.target := c.symm.injOn
  have h_symm_image_inf : (c.symm '' c.target).Infinite :=
    h_tgt_inf.image h_inj_symm
  refine Set.infinite_univ_iff.mp ?_
  exact h_symm_image_inf.mono (Set.subset_univ _)

end Manifold

/-! ## The unconditional discharge of `NearbyRegularWitnessHypothesis` -/

namespace ContMDiff
namespace Owed.degree

universe u v

open JacobianChallenge.Manifold

/-- **Unconditional discharge of `NearbyRegularWitnessHypothesis X Y`.**

For every non-constant `C^ω` map `f : X → Y` between compact connected
complex 1-manifolds and every `y : Y`, there exists a regular-value
witness `w : RegularValueWitnessReg f` whose fibre cardinality equals
the sum of local ramification indices over the fibre of `y`. -/
theorem nearbyRegularWitnessHypothesis_holds_unconditional
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y] :
    NearbyRegularWitnessHypothesis X Y := by
  classical
  intro f hf hnc y
  -- Step 1: fibre F over y is finite.
  have hF_fin : (f ⁻¹' {y}).Finite :=
    fibres_finite_statement_holds_unconditional f hf hnc y
  set F : Set X := f ⁻¹' {y} with hF_def
  -- The toFinset of F.
  set FF : Finset X := hF_fin.toFinset with hFF_def
  -- Step 2: t2-separator W on the finite F (as a Set in T2 X).
  obtain ⟨W, hW_mem_open, hW_disj⟩ := exists_disjoint_open_nbhds_of_finite hF_fin
  -- For each x ∈ F, manifoldRamificationIndex f x ≥ 1.
  have h_perChartNonConst :
      JacobianChallenge.ContMDiff.Owed.degree.PerChartNonConstancyHypothesis X Y :=
    JacobianChallenge.ContMDiff.Owed.degree.perChartNonConstancy_of_clopennessOfLocallyConst
      JacobianChallenge.ContMDiff.Owed.degree.clopennessOfLocallyConst_holds
  -- Step 3: per-x, build a chart-disk D_x ⊆ W x with count = k_x.
  -- For x ∈ F, find R_x > 0 such that:
  --   * Metric.ball ((chartAt ℂ x) x) R_x ⊆ (chartAt ℂ x).target,
  --   * (chartAt ℂ x).symm '' (Metric.ball ((chartAt ℂ x) x) R_x ∩ (chartAt ℂ x).target) ⊆ W x.
  -- Then apply the radius-bounded count to get ε_x ≤ R_x and V_x.
  -- Rather than packaging Σ-type, use Classical.choice through `∀ x ∈ FF, ∃ ...`.
  have h_per_x : ∀ x ∈ FF, ∃ (ε : ℝ) (V : Set Y),
      0 < ε ∧ IsOpen V ∧ f x ∈ V ∧
        ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε) ⊆ W x ∧
        (∀ w ∈ V, w ≠ f x →
          (f ⁻¹' {w} ∩
            ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
            = manifoldRamificationIndex f x) := by
    intro x hxFF
    have hxF : x ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hxFF
    have hxy : f x = y := hxF
    -- Positivity of ramification index.
    have hpos : 1 ≤ manifoldRamificationIndex f x :=
      manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
        h_perChartNonConst hf hnc hxy
    -- Pick W_x := W x.
    have hxWx : x ∈ W x := (hW_mem_open x hxF).1
    have hWx_open : IsOpen (W x) := (hW_mem_open x hxF).2
    -- Find R_x > 0 with chart-ball image in W x.
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
    have hxc : x ∈ c.source := mem_chart_source ℂ x
    -- Need an R such that (c.symm '' Metric.ball (c x) R) ∩ c.source ⊆ W x.
    -- Using continuity of c.symm at c x.
    have h_target_nhds : c.target ∈ 𝓝 (c x) :=
      c.open_target.mem_nhds (c.map_source hxc)
    have h_symm_cx : c.symm (c x) = x := c.left_inv hxc
    have h_symm_cont : ContinuousAt c.symm (c x) := by
      have h_co : ContinuousOn c.symm c.target := c.continuousOn_invFun
      exact h_co.continuousAt h_target_nhds
    -- The set c.symm ⁻¹' (W x ∩ c.source), intersected with c.target, is in 𝓝 (c x).
    have h_pre_nhds : c.symm ⁻¹' (W x) ∈ 𝓝 (c x) := by
      have ht := h_symm_cont.tendsto
      rw [h_symm_cx] at ht
      exact ht (hWx_open.mem_nhds hxWx)
    have h_inter_nhds : c.target ∩ c.symm ⁻¹' (W x) ∈ 𝓝 (c x) :=
      Filter.inter_mem h_target_nhds h_pre_nhds
    obtain ⟨R₀, hR₀_pos, hR₀_sub⟩ := Metric.mem_nhds_iff.mp h_inter_nhds
    -- Apply the radius-bounded count.
    obtain ⟨ε, V, hε_pos, hε_le_R₀, hV_open, h_fx_V, h_count⟩ :=
      localKFoldMultiplicityOnManifold_genuine_with_radius hf x hpos hR₀_pos
    -- D_x ⊆ W x: any z ∈ c.source ∩ c⁻¹' ball (c x) ε has c z ∈ ball (c x) ε ⊆ ball (c x) R₀.
    -- That is in c.target ∩ c.symm ⁻¹' W x. So c.symm (c z) ∈ W x. But c.symm (c z) = z.
    have h_Dx_sub_W :
        ((c.source ∩ c ⁻¹' Metric.ball (c x) ε) : Set X) ⊆ W x := by
      intro z hz
      obtain ⟨hz_src, hz_ball⟩ := hz
      have hcz_target_W : c z ∈ c.target ∩ c.symm ⁻¹' W x :=
        hR₀_sub (Metric.ball_subset_ball hε_le_R₀ hz_ball)
      have hcz_pre : c.symm (c z) ∈ W x := hcz_target_W.2
      have hsymm_cz : c.symm (c z) = z := c.left_inv hz_src
      rw [hsymm_cz] at hcz_pre
      exact hcz_pre
    refine ⟨ε, V, hε_pos, hV_open, h_fx_V, ?_, h_count⟩
    -- Goal: ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε) ⊆ W x.
    -- This is exactly h_Dx_sub_W (c is chartAt ℂ x by definition).
    exact h_Dx_sub_W
  -- Use AxiomOfChoice to pick per-x witnesses.
  choose ε_fn V_fn hε_pos_fn hV_open_fn h_fx_V_fn h_Dx_sub_W_fn h_count_fn using h_per_x
  -- Step 4: define D_x : X → Set X.
  set D_x : X → Set X := fun x' =>
    (chartAt ℂ x').source ∩ (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
      if h : x' ∈ FF then ε_fn x' h else 0) with hD_def
  -- D_x for x ∈ F is open.
  have hD_open : ∀ x' ∈ FF, IsOpen (D_x x') := by
    intro x' hx'F
    show IsOpen ((chartAt ℂ x').source ∩
      (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
        if h : x' ∈ FF then ε_fn x' h else 0))
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'F from dif_pos hx'F]
    have hco : ContinuousOn (chartAt ℂ x') (chartAt ℂ x').source :=
      (chartAt ℂ x').continuousOn_toFun
    exact hco.isOpen_inter_preimage (chartAt ℂ x').open_source Metric.isOpen_ball
  -- x' ∈ D_x x'.
  have hxD : ∀ x' ∈ FF, x' ∈ D_x x' := by
    intro x' hx'F
    show x' ∈ (chartAt ℂ x').source ∩
      (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
        if h : x' ∈ FF then ε_fn x' h else 0)
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'F from dif_pos hx'F]
    refine ⟨mem_chart_source ℂ x', ?_⟩
    show (chartAt ℂ x') x' ∈ Metric.ball ((chartAt ℂ x') x') (ε_fn x' hx'F)
    exact Metric.mem_ball_self (hε_pos_fn x' hx'F)
  -- D_x ⊆ W x'.
  have hD_sub_W : ∀ x' ∈ FF, D_x x' ⊆ W x' := by
    intro x' hx'F
    show ((chartAt ℂ x').source ∩
      (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
        if h : x' ∈ FF then ε_fn x' h else 0)) ⊆ W x'
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'F from dif_pos hx'F]
    exact h_Dx_sub_W_fn x' hx'F
  -- D_x is pairwise disjoint (inherits from W x' disjointness).
  have hD_pwd : F.PairwiseDisjoint D_x := by
    intro a haF b hbF hab
    have haFF : a ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using haF
    have hbFF : b ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using hbF
    have hWab : Disjoint (W a) (W b) := hW_disj haF hbF hab
    have hDa_sub : D_x a ⊆ W a := hD_sub_W a haFF
    have hDb_sub : D_x b ⊆ W b := hD_sub_W b hbFF
    show Disjoint (D_x a) (D_x b)
    exact hWab.mono hDa_sub hDb_sub
  -- Step 5: apply preimage_eventually_in_fibre_neighbourhoods with U := D_x.
  have hf_cont : Continuous f := hf.continuous
  -- Need (∀ x ∈ F, IsOpen (D_x x)) and (∀ x ∈ F, x ∈ D_x x).
  have hD_open_F : ∀ x' ∈ F, IsOpen (D_x x') := by
    intro x' hx'F
    have hx'FF : x' ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'F
    exact hD_open x' hx'FF
  have hxD_F : ∀ x' ∈ F, x' ∈ D_x x' := by
    intro x' hx'F
    have hx'FF : x' ∈ FF := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'F
    exact hxD x' hx'FF
  obtain ⟨V₀, hV₀_open, hyV₀, hV₀_sub⟩ :=
    JacobianChallenge.PreimageEventualContainment.preimage_eventually_in_fibre_neighbourhoods
      hf_cont y hF_fin D_x hD_open_F hxD_F
  -- Define a per-x-with-default V function, so we can intersect with a uniform interface.
  set V_fn' : X → Set Y := fun x' =>
    if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y) with hV_fn'_def
  have hV_fn'_open : ∀ x' ∈ FF, IsOpen (V_fn' x') := by
    intro x' hx'FF
    show IsOpen (if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y))
    rw [dif_pos hx'FF]; exact hV_open_fn x' hx'FF
  have hV_fn'_y : ∀ x' ∈ FF, y ∈ V_fn' x' := by
    intro x' hx'FF
    have hx'F : x' ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'FF
    have hxy : f x' = y := hx'F
    show y ∈ (if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y))
    rw [dif_pos hx'FF]
    have := h_fx_V_fn x' hx'FF
    rw [hxy] at this
    exact this
  -- V_inter := intersection over FF.
  set V_inter : Set Y := V₀ ∩ (⋂ x' ∈ FF, V_fn' x') with hV_inter_def
  have hV_inter_open : IsOpen V_inter := by
    refine hV₀_open.inter ?_
    refine isOpen_biInter_finset ?_
    intro x' hx'FF
    exact hV_fn'_open x' hx'FF
  have hy_V_inter : y ∈ V_inter := by
    refine ⟨hyV₀, ?_⟩
    rw [Set.mem_iInter₂]
    intro x' hx'FF
    exact hV_fn'_y x' hx'FF
  -- Step 7: Final V := V_inter \ ((criticalValuesGeneral f) ∪ {y}).
  -- Need: V is non-empty. V_inter is open, contains y, and we remove a finite set.
  have h_cv_fin : (criticalValuesGeneral f).Finite :=
    criticalValues_finite_general f hf hnc
  have h_remove_fin : ((criticalValuesGeneral f) ∪ ({y} : Set Y)).Finite :=
    h_cv_fin.union (Set.finite_singleton y)
  -- V_inter is infinite (open in a complex 1-manifold, contains a point).
  haveI : Infinite Y := y_infinite_of_chartedSpace_complex_local
  -- Show V_inter is infinite using openness + chart trick.
  have hV_inter_inf : V_inter.Infinite := by
    -- It's an open neighbourhood of y in Y, push to chart.
    set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ y with hd_def
    have hyd : y ∈ d.source := mem_chart_source ℂ y
    have hd_target_nhds : d.target ∈ 𝓝 (d y) :=
      d.open_target.mem_nhds (d.map_source hyd)
    have h_co : ContinuousOn d.symm d.target := d.continuousOn_invFun
    have h_symm_dy : d.symm (d y) = y := d.left_inv hyd
    have h_symm_cont : ContinuousAt d.symm (d y) := h_co.continuousAt hd_target_nhds
    have h_pre_nhds : d.symm ⁻¹' V_inter ∈ 𝓝 (d y) := by
      have ht := h_symm_cont.tendsto
      rw [h_symm_dy] at ht
      exact ht (hV_inter_open.mem_nhds hy_V_inter)
    have h_combo_nhds : d.target ∩ d.symm ⁻¹' V_inter ∈ 𝓝 (d y) :=
      Filter.inter_mem hd_target_nhds h_pre_nhds
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
    -- The ball of radius ρ in ℂ is infinite.
    have h_ball_inf : (Metric.ball (d y) ρ).Infinite :=
      isOpen_complex_set_infinite_of_mem_local Metric.isOpen_ball
        (Metric.mem_ball_self hρ_pos)
    -- Image under d.symm of the ball lies in V_inter ∩ d.target.
    -- The image is also infinite because d.symm is injective on d.target.
    have h_inj_on : Set.InjOn d.symm (Metric.ball (d y) ρ) := by
      intro a ha b hb hab
      have ha_target : a ∈ d.target := (hρ_sub ha).1
      have hb_target : b ∈ d.target := (hρ_sub hb).1
      have ha_eq : d (d.symm a) = a := d.right_inv ha_target
      have hb_eq : d (d.symm b) = b := d.right_inv hb_target
      rw [hab] at ha_eq
      exact ha_eq.symm.trans hb_eq
    have h_image_inf : (d.symm '' Metric.ball (d y) ρ).Infinite :=
      h_ball_inf.image h_inj_on
    -- And the image is a subset of V_inter.
    have h_image_sub : d.symm '' Metric.ball (d y) ρ ⊆ V_inter := by
      rintro y' ⟨z, hz_ball, hz_eq⟩
      have hz_sub := hρ_sub hz_ball
      have hz_pre : z ∈ d.symm ⁻¹' V_inter := hz_sub.2
      rw [← hz_eq]
      exact hz_pre
    exact h_image_inf.mono h_image_sub
  -- V_inter \ remove is infinite (infinite minus finite).
  have hV_diff_inf : (V_inter \ ((criticalValuesGeneral f) ∪ ({y} : Set Y))).Infinite := by
    intro hfin
    have h_union : V_inter ⊆ (V_inter \ ((criticalValuesGeneral f) ∪ ({y} : Set Y))) ∪
        ((criticalValuesGeneral f) ∪ ({y} : Set Y)) := by
      intro a haV
      by_cases h : a ∈ (criticalValuesGeneral f) ∪ ({y} : Set Y)
      · exact Or.inr h
      · exact Or.inl ⟨haV, h⟩
    have hV_inter_fin : V_inter.Finite :=
      (hfin.union h_remove_fin).subset h_union
    exact hV_inter_inf hV_inter_fin
  obtain ⟨w, hwV_inter, hw_notin⟩ := hV_diff_inf.nonempty
  -- hw_notin : w ∉ criticalValuesGeneral f ∪ {y}.
  have hw_not_cv : w ∉ criticalValuesGeneral f := fun hw_cv => hw_notin (Or.inl hw_cv)
  have hw_ne_y : w ≠ y := fun hw_eq => hw_notin (Or.inr hw_eq)
  -- Step 8: extract w properties.
  have hw_V₀ : w ∈ V₀ := hwV_inter.1
  have hw_V_fn' : ∀ x' ∈ FF, w ∈ V_fn' x' := by
    intro x' hx'FF
    have := hwV_inter.2
    rw [Set.mem_iInter₂] at this
    exact this x' hx'FF
  have hw_V_fn : ∀ x' (hx'FF : x' ∈ FF), w ∈ V_fn x' hx'FF := by
    intro x' hx'FF
    have hwV' := hw_V_fn' x' hx'FF
    show w ∈ V_fn x' hx'FF
    have : V_fn' x' = V_fn x' hx'FF := by
      show (if h : x' ∈ FF then V_fn x' h else (Set.univ : Set Y)) = V_fn x' hx'FF
      rw [dif_pos hx'FF]
    rw [this] at hwV'
    exact hwV'
  -- Step 9: f⁻¹{w} ⊆ ⋃ x' ∈ FF, D_x x'.
  have hpre_w_sub : f ⁻¹' {w} ⊆ ⋃ x' ∈ FF, D_x x' := by
    intro z hz
    have hz_V₀ : z ∈ f ⁻¹' V₀ := by
      show f z ∈ V₀
      have hfz : f z = w := hz
      rw [hfz]; exact hw_V₀
    exact hV₀_sub hz_V₀
  -- Step 10: f⁻¹{w} is finite (regular value, sub of finite union of D_x).
  -- Each D_x has count k_x preimages of w; the union has at most ∑ k_x preimages.
  -- Actually let's directly compute |f⁻¹{w}| = ∑ k_x.
  -- (a) f⁻¹{w} = ⋃ x' ∈ FF, (f⁻¹{w} ∩ D_x x') (disjoint).
  have hpre_w_eq : f ⁻¹' {w} = ⋃ x' ∈ FF, (f ⁻¹' {w} ∩ D_x x') := by
    ext z
    constructor
    · intro hz
      have hz_in_union : z ∈ ⋃ x' ∈ FF, D_x x' := hpre_w_sub hz
      rw [Set.mem_iUnion₂] at hz_in_union
      obtain ⟨x', hx'FF, hzD⟩ := hz_in_union
      rw [Set.mem_iUnion₂]
      exact ⟨x', hx'FF, hz, hzD⟩
    · rintro hz
      rw [Set.mem_iUnion₂] at hz
      obtain ⟨x', _, hz_pre, _⟩ := hz
      exact hz_pre
  -- (b) The pieces are pairwise disjoint (inherits from D_x disjointness).
  have h_pieces_pwd :
      (FF : Set X).PairwiseDisjoint (fun x' => f ⁻¹' {w} ∩ D_x x') := by
    intro a haFF b hbFF hab
    have haF : a ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using haFF
    have hbF : b ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hbFF
    have h := hD_pwd haF hbF hab
    show Disjoint (f ⁻¹' {w} ∩ D_x a) (f ⁻¹' {w} ∩ D_x b)
    exact h.mono Set.inter_subset_right Set.inter_subset_right
  -- (c) Each piece (f⁻¹{w} ∩ D_x x').ncard = manifoldRamificationIndex f x'.
  have h_piece_card : ∀ x' ∈ FF,
      (f ⁻¹' {w} ∩ D_x x').ncard = manifoldRamificationIndex f x' := by
    intro x' hx'FF
    have hx'F : x' ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'FF
    have hxy : f x' = y := hx'F
    have hwV' : w ∈ V_fn x' hx'FF := hw_V_fn x' hx'FF
    have hw_ne_fx' : w ≠ f x' := by rw [hxy]; exact hw_ne_y
    have hcount := h_count_fn x' hx'FF w hwV' hw_ne_fx'
    -- Need to identify D_x x' with the D-set in h_count_fn's conclusion.
    show (f ⁻¹' {w} ∩
      ((chartAt ℂ x').source ∩
        (chartAt ℂ x') ⁻¹' Metric.ball ((chartAt ℂ x') x') (
          if h : x' ∈ FF then ε_fn x' h else 0))).ncard
        = manifoldRamificationIndex f x'
    rw [show (if h : x' ∈ FF then ε_fn x' h else 0) = ε_fn x' hx'FF from dif_pos hx'FF]
    exact hcount
  -- (d) Each piece is finite (count is finite).
  have h_piece_fin : ∀ x' ∈ FF, (f ⁻¹' {w} ∩ D_x x').Finite := by
    intro x' hx'FF
    have h_card := h_piece_card x' hx'FF
    by_cases hk0 : manifoldRamificationIndex f x' = 0
    · -- card is 0; the set could still be infinite. Need another argument.
      -- But manifoldRamificationIndex f x' ≥ 1 (positivity), so this case is moot.
      have hx'F : x' ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hx'FF
      have hxy : f x' = y := hx'F
      have hpos : 1 ≤ manifoldRamificationIndex f x' :=
        manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
          h_perChartNonConst hf hnc hxy
      omega
    · exact Set.finite_of_ncard_ne_zero (by rw [h_card]; exact hk0)
  -- (e) f⁻¹{w} is finite.
  have hpre_w_fin : (f ⁻¹' {w}).Finite := by
    rw [hpre_w_eq]
    refine Set.Finite.biUnion (Set.toFinite (FF : Set X)) ?_
    intro x' hx'FF
    have hx'FF' : x' ∈ FF := hx'FF
    exact h_piece_fin x' hx'FF'
  -- (f) Sum: |f⁻¹{w}| = ∑ x' ∈ FF, |f⁻¹{w} ∩ D_x x'|.
  -- Proof: convert the biUnion into a Finset.biUnion over disjoint sets.
  have h_sum_ncard :
      (f ⁻¹' {w}).ncard =
        ∑ x' ∈ FF, (f ⁻¹' {w} ∩ D_x x').ncard := by
    have hbiU_fin : (⋃ x' ∈ FF, (f ⁻¹' {w} ∩ D_x x')).Finite :=
      Set.Finite.biUnion (Set.toFinite (FF : Set X))
        (fun x' hx'FF => h_piece_fin x' hx'FF)
    -- Convert the goal to Finset.card.
    rw [hpre_w_eq, Set.ncard_eq_toFinset_card _ hbiU_fin]
    -- The toFinset of a biUnion of disjoint pieces equals the Finset.biUnion.
    -- Use that explicitly via Finset.card_biUnion + disjointness.
    -- Define: g : X → Finset X := fun x' => (h_piece_fin x' (Classical.byContradiction ...)).toFinset
    -- Better: use Finset.sum_card via the existing finset.
    -- Approach: show the toFinset equals Finset.biUnion FF (fun x' => piece x'), then Finset.card_biUnion.
    -- Each piece's finiteness is local; classical.choice / dependent function.
    classical
    -- Key: for each x' in FF, let pieceF x' := (h_piece_fin x' h).toFinset for h ∈ FF, else ∅.
    set pieceF : X → Finset X := fun x' =>
      if h : x' ∈ FF then (h_piece_fin x' h).toFinset else (∅ : Finset X) with hpieceF_def
    have hpieceF_card : ∀ x' ∈ FF,
        (pieceF x').card = (f ⁻¹' {w} ∩ D_x x').ncard := by
      intro x' hx'FF
      show (if h : x' ∈ FF then (h_piece_fin x' h).toFinset else (∅ : Finset X)).card
        = (f ⁻¹' {w} ∩ D_x x').ncard
      rw [dif_pos hx'FF]
      exact (Set.ncard_eq_toFinset_card _ (h_piece_fin x' hx'FF)).symm
    -- Show toFinset of biUnion = FF.biUnion pieceF.
    have htoFinset_eq :
        hbiU_fin.toFinset = FF.biUnion pieceF := by
      ext z
      rw [Set.Finite.mem_toFinset, Finset.mem_biUnion]
      constructor
      · intro hz
        rw [Set.mem_iUnion₂] at hz
        obtain ⟨x', hx'FF, hzD⟩ := hz
        refine ⟨x', hx'FF, ?_⟩
        show z ∈ (if h : x' ∈ FF then (h_piece_fin x' h).toFinset else (∅ : Finset X))
        rw [dif_pos hx'FF, Set.Finite.mem_toFinset]
        exact hzD
      · rintro ⟨x', hx'FF, hzpc⟩
        rw [show pieceF x' = (h_piece_fin x' hx'FF).toFinset from
          show (if h : x' ∈ FF then (h_piece_fin x' h).toFinset else (∅ : Finset X))
            = (h_piece_fin x' hx'FF).toFinset from dif_pos hx'FF] at hzpc
        rw [Set.Finite.mem_toFinset] at hzpc
        rw [Set.mem_iUnion₂]
        exact ⟨x', hx'FF, hzpc⟩
    rw [htoFinset_eq]
    -- pairwise disjoint.
    have hpieceF_disj : (FF : Set X).PairwiseDisjoint pieceF := by
      intro a haFF b hbFF hab
      have haF : a ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using haFF
      have hbF : b ∈ F := by simpa [hFF_def, Set.Finite.mem_toFinset] using hbFF
      have hDab : Disjoint (D_x a) (D_x b) := hD_pwd haF hbF hab
      show Disjoint (pieceF a) (pieceF b)
      have hpcA : pieceF a = (h_piece_fin a haFF).toFinset := dif_pos haFF
      have hpcB : pieceF b = (h_piece_fin b hbFF).toFinset := dif_pos hbFF
      rw [hpcA, hpcB]
      rw [Finset.disjoint_left]
      intro z hzA hzB
      rw [Set.Finite.mem_toFinset] at hzA hzB
      have hzA_D : z ∈ D_x a := hzA.2
      have hzB_D : z ∈ D_x b := hzB.2
      exact hDab.le_bot ⟨hzA_D, hzB_D⟩
    rw [Finset.card_biUnion (fun a haFF b hbFF hab =>
      hpieceF_disj haFF hbFF hab)]
    apply Finset.sum_congr rfl
    intro x' hx'FF
    exact hpieceF_card x' hx'FF
  -- Step 11: Build the regular witness.
  -- w is regular: at every preimage x' of w, deriv chart-pullback ≠ 0.
  have h_reg : ∀ x' ∈ f ⁻¹' {w},
      deriv ((chartAt ℂ w) ∘ f ∘ (chartAt ℂ x').symm)
        ((chartAt ℂ x') x') ≠ 0 := by
    intro x' hx'
    exact deriv_chart_pullback_ne_zero_at_regular_preimage hf hnc hw_not_cv hx'
  let w_witness : RegularValueWitness f :=
    { value := w, fiber_finite := hpre_w_fin }
  let w_reg : RegularValueWitnessReg f := w_witness.toRegular h_reg
  refine ⟨w_reg, ?_⟩
  -- Show w_reg.card = ∑ x ∈ hF_fin.toFinset, manifoldRamificationIndex f x.
  show (w_reg.card : ℕ) =
    ∑ x ∈ (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
      manifoldRamificationIndex f x
  -- w_reg.card = w_witness.card = hpre_w_fin.toFinset.card = (f⁻¹{w}).ncard.
  have h_card_eq : (w_reg.card : ℕ) = (f ⁻¹' {w}).ncard := by
    show w_witness.card = (f ⁻¹' {w}).ncard
    show hpre_w_fin.toFinset.card = (f ⁻¹' {w}).ncard
    exact (Set.ncard_eq_toFinset_card _ hpre_w_fin).symm
  rw [h_card_eq, h_sum_ncard]
  -- Goal: ∑ x' ∈ FF, (f⁻¹{w} ∩ D_x x').ncard
  --     = ∑ x ∈ (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset,
  --        manifoldRamificationIndex f x
  -- The toFinset on the RHS equals FF (since both = hF_fin.toFinset).
  have hFF_eq : (fibres_finite_statement_holds_unconditional f hf hnc y).toFinset = FF := by
    rfl
  rw [hFF_eq]
  apply Finset.sum_congr rfl
  intro x' hx'FF
  exact h_piece_card x' hx'FF

/-! ## Headline corollary -/

/-- **Unconditional discharge of `ramificationSumEqualsDegree_statement`.**

This is the named obligation `Owed.degree.ramificationSumEqualsDegree_statement X Y`,
discharged by composing the unconditional `wd_reg_holds_unconditional` (from
`RamificationSumEqualsDegreeUnconditional.lean`) with the unconditional
`nearbyRegularWitnessHypothesis_holds_unconditional` shipped above. -/
theorem ramificationSumEqualsDegree_holds_unconditional
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (Y : Type v) [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold (𝓘(ℂ, ℂ)) ω Y] :
    JacobianChallenge.ContMDiff.Owed.degree.ramificationSumEqualsDegree_statement X Y :=
  ramificationSumEqualsDegree_holds_of_nearby_regular_witness_only
    (nearbyRegularWitnessHypothesis_holds_unconditional X Y)

end Owed.degree
end ContMDiff
end JacobianChallenge

end

end
