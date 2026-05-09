/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalKFoldMultiplicityFullyUnconditional
import JacobianChallenge.Manifold.LocalKFoldMultiplicityUnconditional
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import JacobianChallenge.Manifold.AnalyticKthRoot
import JacobianChallenge.Manifold.RamificationIndex
import JacobianChallenge.Manifold.RamificationIndexEqLocalKFold
import JacobianChallenge.Manifold.ContMDiffOmegaAnalytic
import JacobianChallenge.Manifold.IsConstantMapAux

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Genuine manifold-level fibre count from chart-pullback k-fold count

The chip ZZ91 (`LocalKFoldMultiplicityChartPullback`) ships the
**chart-pullback** `k`-fold count over `ftilde : X → RiemannSphere`. Several
files (`LocalCountPackageSupplier`, `LocalCountPackageInputsDischarge`,
`LocalKFoldMultiplicityChartPullback`, `HurwitzPatchingDataConstruction`)
flag the residual: lifting the planar `ε`-disc count via `(chartAt ℂ x).symm`
to a count in `X` itself.

This file discharges that residual for `f : X → Y` between charted spaces
modelled on `ℂ`.

## What this file ships

* `localKFoldMultiplicity_preimage_card_with_radius_bound` — variant of
  `localKFoldMultiplicity_preimage_card_fully_unconditional` that accepts a
  user-supplied upper bound `R` on the output `ε`. Built by shrinking the
  factorization radius before threading through the substitution count.

* `localKFoldMultiplicityOnManifold_genuine_preimage_card` — the headline.
  For `f : X → Y` real-analytic and a point `x : X` with `1 ≤
  manifoldRamificationIndex f x`, there exist an open chart-disc `D_x` around
  `x` and an open neighbourhood `V` of `f x` in `Y` such that for every
  `w ∈ V \ {f x}`,
  `(f ⁻¹' {w} ∩ D_x).ncard = manifoldRamificationIndex f x`.

The disc `D_x` is the chart-symm image of an open `ε`-ball in chart
coordinates, intersected with the chart source. The neighbourhood `V` is
the chart-symm image of an open `δ`-ball around `(chartAt ℂ (f x)) (f x)`,
intersected with the chart source at `f x`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature changes outside this new file.
* The chart-bijection transport uses `Set.ncard_image_of_injOn` and the
  partial-homeomorph injectivity / left-inverse from mathlib.
* The radius-bound helper is a local refinement of the planar fully
  unconditional count; it does not change any signature outside this file.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric Function
open scoped Manifold Topology ContDiff

namespace JacobianChallenge
namespace Manifold

universe u v

/-! ## Helper: planar `k`-fold count with a user-supplied radius bound -/

/-- **Planar `k`-fold count with `ε ≤ R`.**

A refinement of `localKFoldMultiplicity_preimage_card_fully_unconditional`
that lets the caller supply an upper bound `R` on the output `ε`. The proof
shrinks the factorization radius produced by `analytic_local_factorization`
to `min` with `R`, then threads through the substitution count which already
respects the radius bound (the `hε_le_ρ` field of
`localMultiplicityOne_preimage_card_with_radius`). -/
private theorem localKFoldMultiplicity_preimage_card_with_radius_bound
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R : ℝ}
    (hk : 1 ≤ k) (hR : 0 < R)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ ε > (0 : ℝ), ε ≤ R ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  -- Step 1: extract the local factorization on some closed disk closedBall x₀ R₀.
  obtain ⟨R₀, hR₀_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  -- Step 2: shrink the factorization radius to `R' = min R₀ R`.
  set R' : ℝ := min R₀ R with hR'_def
  have hR'_pos : 0 < R' := lt_min hR₀_pos hR
  have hR'_le_R₀ : R' ≤ R₀ := min_le_left _ _
  have hR'_le_R : R' ≤ R := min_le_right _ _
  -- The factorization restricts to closedBall x₀ R'.
  have hu_an' : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R') :=
    fun z hz => hu_an z (Metric.closedBall_subset_closedBall hR'_le_R₀ hz)
  have hfact' : ∀ z ∈ Metric.closedBall x₀ R',
      g z - w₀ = (z - x₀) ^ k * u z :=
    fun z hz => hfact z (Metric.closedBall_subset_closedBall hR'_le_R₀ hz)
  -- Step 3: extract analytic k-th root of `u` directly, retaining the radius bound.
  obtain ⟨r, ρ_v, hρ_v_pos, hρ_v_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR'_pos hu_an' hu_x₀ hk
  -- The substitution function we use is `v_actual := fun z => (z - x₀) * r z`
  -- with substitution radius `ρ_v ≤ R'`.
  set v_actual : ℂ → ℂ := fun z => (z - x₀) * r z with hvact_def
  -- Verify the substitution bundle properties for `v_actual` on closedBall x₀ ρ_v.
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
    rw [h1, ← h2, mul_pow, hvact_def]
  -- Apply ZZ74-with-radius (on `v_actual`).
  have hva_at_x₀ : AnalyticAt ℂ v_actual x₀ :=
    hva_an x₀ (Metric.mem_closedBall_self hρ_v_pos.le)
  obtain ⟨ε, hε_pos, hε_le_ρv, δ₁, hδ₁_pos, hZZ74_v⟩ :=
    localMultiplicityOne_preimage_card_with_radius hva_at_x₀ hva_d hρ_v_pos
  -- Ship: ε ≤ ρ_v ≤ R' ≤ R.
  have hε_le_R : ε ≤ R := hε_le_ρv.trans (hρ_v_le.trans hR'_le_R)
  -- Build δ. (Mirror the structure of
  -- `localKFoldMultiplicity_preimage_card_of_substitution`.)
  rw [show v_actual x₀ = 0 from hva_x₀] at hZZ74_v
  set δ : ℝ := (δ₁ / 2) ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos (by linarith) k
  refine ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, ?_⟩
  -- Now mimic the count-from-substitution bookkeeping.
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
  -- Bijection bookkeeping: reproduce the standard substitution argument inline.
  set Pre : Set ℂ := {z ∈ Metric.ball x₀ ε | g z = w} with hPre_def
  set Fset : Finset ℂ := (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).roots.toFinset
    with hFset_def
  -- Bijection `z ↦ v_actual z` between `Pre` and `(Fset : Set ℂ)`.
  -- `hZZ74_v` gives uniqueness for ξ ∈ ball 0 δ₁ \ {0}.
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
    -- v_actual z is a root of `X^k - C w₁`.
    have hroot : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).IsRoot (v_actual z) := by
      unfold Polynomial.IsRoot
      simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero, hvk]
    -- And the polynomial is nonzero.
    have hp_ne : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ) ≠ 0 := by
      intro hh
      have hdeg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
        Polynomial.natDegree_X_pow_sub_C
      rw [hh] at hdeg
      simp at hdeg
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      exact hk0 hdeg.symm
    rw [hFset_def, Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
    exact hroot
  have h_v_count : ∀ ξ ∈ Fset, ({z ∈ Metric.ball x₀ ε | v_actual z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξ
    rw [hFset_def, Multiset.mem_toFinset] at hξ
    have hp_ne : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ) ≠ 0 := by
      intro hh
      have hdeg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
        Polynomial.natDegree_X_pow_sub_C
      rw [hh] at hdeg
      simp at hdeg
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      exact hk0 hdeg.symm
    rw [Polynomial.mem_roots hp_ne] at hξ
    have hξk : ξ ^ k = w₁ := by
      have := hξ
      unfold Polynomial.IsRoot at this
      simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero] at this
      exact this
    have hξ_ne : ξ ≠ 0 := h_roots_ne ξ hξk
    have hξ_norm : ‖ξ‖ < δ₁ := h_roots_small ξ hξk
    have hξ_ball : ξ ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hξ_norm
    exact hZZ74_v ξ hξ_ball hξ_ne
  -- Existence and injectivity (mirror of the main count proof).
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
    rw [hFset_def, Multiset.mem_toFinset] at hξ
    have hp_ne : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ) ≠ 0 := by
      intro hh
      have hdeg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
        Polynomial.natDegree_X_pow_sub_C
      rw [hh] at hdeg
      simp at hdeg
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      exact hk0 hdeg.symm
    rw [Polynomial.mem_roots hp_ne] at hξ
    have hξk : ξ ^ k = w₁ := by
      have := hξ
      unfold Polynomial.IsRoot at this
      simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_C, sub_eq_zero] at this
      exact this
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
  -- Cardinality.
  have hF_card : Fset.card = k := by
    have hp_ne : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ) ≠ 0 := by
      intro hh
      have hdeg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
        Polynomial.natDegree_X_pow_sub_C
      rw [hh] at hdeg
      simp at hdeg
      have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
      exact hk0 hdeg.symm
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    have hp_deg : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).natDegree = k :=
      Polynomial.natDegree_X_pow_sub_C
    have h_separable : (Polynomial.X ^ k - Polynomial.C w₁ : Polynomial ℂ).Separable := by
      exact Polynomial.separable_X_pow_sub_C w₁ (by exact_mod_cast hk0) hw₁_ne
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
      (Set.ncard_image_of_injOn h_v_injOn).symm
    rw [h1, h_image_eq, Set.ncard_coe_finset]
  rw [hPre_ncard, hF_card]

/-! ## Headline: genuine manifold-level fibre count -/

/-- **Genuine manifold-level fibre count from the chart-pullback `k`-fold count.**

For a real-analytic map `f : X → Y` between charted spaces over `ℂ` and a
basepoint `x : X` with positive ramification index, there exist:

* an open chart-disc `D_x` around `x` in `X` (the `(chartAt ℂ x).symm` image
  of an open `ε`-ball, intersected with the chart source),
* an open neighbourhood `V` of `f x` in `Y`,

such that for every `w ∈ V \ {f x}`,
`(f ⁻¹' {w} ∩ D_x).ncard = manifoldRamificationIndex f x`.

This is the residual flagged by `LocalKFoldMultiplicityChartPullback`,
`LocalCountPackageSupplier`, and `LocalCountPackageInputsDischarge`: the
chart-bijection lift of the planar `ε-δ` count to a count in the manifold
itself.

Hypotheses:

* `hf` — `f` is real-analytic everywhere (`ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω`). This
  supplies `AnalyticAt ℂ` of the chart pullback at the chart image of `x`.
* `hpos` — the ramification index at `x` is at least `1`. This excludes the
  locally-constant case (`analyticOrderAt = ⊤`) and, together with the
  definition `manifoldRamificationIndex = .toNat`, lets us identify the
  `ENat`-valued analytic order with `(k : ℕ∞)` for `k = manifoldRamificationIndex f x`.
  In the non-constant `f` case this hypothesis is supplied by
  `manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy`. -/
theorem localKFoldMultiplicityOnManifold_genuine_preimage_card
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X)
    (hpos : 1 ≤ manifoldRamificationIndex f x) :
    ∃ (ε : ℝ) (V : Set Y), 0 < ε ∧ IsOpen V ∧ f x ∈ V ∧
      (∀ w ∈ V, w ≠ f x →
        (f ⁻¹' {w} ∩
          ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) ε)).ncard
          = manifoldRamificationIndex f x) := by
  classical
  -- Notation.
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀_def
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF_def
  set k : ℕ := manifoldRamificationIndex f x with hk_def
  -- F is analytic at z₀.
  have hF_an : AnalyticAt ℂ F z₀ :=
    JacobianChallenge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- F z₀ = (chartAt (f x)) (f x).
  have hF_z₀_eq : F z₀ = (chartAt ℂ (f x)) (f x) := by
    have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        = (chartAt ℂ (f x)) (f x)
    simp [Function.comp, (chartAt ℂ x).left_inv hx_src]
  -- From `1 ≤ k = (analyticOrderAt (F - F z₀) z₀).toNat`, the order is
  -- `(k : ℕ∞)`. Two cases: order = ⊤ or = (n : ℕ∞).
  have hord : analyticOrderAt (fun z => F z - F z₀) z₀ = (k : ℕ∞) := by
    have hk_eq : k = (analyticOrderAt (fun z => F z - F z₀) z₀).toNat := rfl
    -- Since 1 ≤ k.toNat, the order must be a finite positive ℕ∞ value.
    set ord : ℕ∞ := analyticOrderAt (fun z => F z - F z₀) z₀ with hord_def
    have hk_toNat : 1 ≤ ord.toNat := by rw [hk_eq] at hpos; exact hpos
    -- ord.toNat ≥ 1 forces ord ≠ 0 and ord ≠ ⊤.
    have hord_ne_top : ord ≠ ⊤ := by
      intro h
      rw [h, ENat.toNat_top] at hk_toNat
      exact absurd hk_toNat (by norm_num)
    have hord_ne_zero : ord ≠ 0 := by
      intro h
      rw [h] at hk_toNat
      simp at hk_toNat
    -- ord = (n : ℕ∞) for some n, and that n equals ord.toNat = k.
    cases hord_eq : ord with
    | top => exact absurd hord_eq hord_ne_top
    | coe n =>
      show ord = (k : ℕ∞)
      rw [hord_eq]
      congr 1
      have hk_n : k = n := by
        rw [hk_eq, hord_eq, ENat.toNat_coe]
      rw [hk_n]
  -- Apply the radius-bounded planar count.
  -- Choose R₀ small enough for chart-target containment AND for f-continuity
  -- to land in the chart source at f x.
  -- (i) Chart target containment: there exists R_t > 0 with ball z₀ R_t ⊆ target(chartAt x).
  have h_target_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
  have hz₀_target : z₀ ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have h_target_nhds : (chartAt ℂ x).target ∈ 𝓝 z₀ :=
    h_target_open.mem_nhds hz₀_target
  obtain ⟨R_t, hR_t_pos, hR_t_sub⟩ := Metric.mem_nhds_iff.mp h_target_nhds
  -- (ii) Continuity: there's R_c > 0 such that for all z ∈ ball z₀ R_c ∩ target,
  -- f((chartAt x).symm z) ∈ source(chartAt(f x)).
  -- Use: F is continuous (analytic ⇒ continuous) at z₀; F z₀ = (chartAt(fx))(fx)
  -- ∈ target(chartAt(fx)). But we want `f((chartAt x).symm z) ∈ source(chartAt(fx))`.
  -- Key fact: at points z ∈ target where (chartAt x).symm z ∈ source ∩
  -- f⁻¹(source(chartAt(fx))), F z is genuinely the chart of f(...).
  -- Because (chartAt(fx)).source contains f x, (chartAt x).source contains x,
  -- and f is continuous, an open set around x lands in f⁻¹(source(chartAt(fx))) ∩ source(chartAt x).
  have h_f_cont : Continuous f := hf.continuous
  -- The set f⁻¹(source(chartAt(fx))) ∩ source(chartAt x) is open and contains x.
  have h_open_x : IsOpen ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) :=
    (chartAt ℂ x).open_source.inter ((chartAt ℂ (f x)).open_source.preimage h_f_cont)
  have h_x_mem : x ∈ (chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source :=
    ⟨mem_chart_source ℂ x, mem_chart_source ℂ (f x)⟩
  -- Image under chartAt x is open (chart is open embedding on source).
  -- Equivalently: by continuity of (chartAt x).symm at z₀, the preimage of
  -- this open set under symm is in 𝓝 z₀.
  have h_symm_cont : ContinuousAt (chartAt ℂ x).symm z₀ := by
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt h_target_nhds
  have h_symm_z₀ : (chartAt ℂ x).symm z₀ = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  -- The preimage `(chartAt x).symm ⁻¹' open_x` is in 𝓝 z₀.
  have h_pre_nhds :
      (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) ∈ 𝓝 z₀ := by
    have ht := h_symm_cont.tendsto
    rw [h_symm_z₀] at ht
    exact ht (h_open_x.mem_nhds h_x_mem)
  -- Combine with target.
  have h_combined :
      (chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) ∈ 𝓝 z₀ :=
    Filter.inter_mem h_target_nhds h_pre_nhds
  obtain ⟨R_c, hR_c_pos, hR_c_sub⟩ := Metric.mem_nhds_iff.mp h_combined
  -- Choose R := min R_t R_c.
  set R : ℝ := min R_t R_c with hR_def
  have hR_pos : 0 < R := lt_min hR_t_pos hR_c_pos
  have hR_le_R_t : R ≤ R_t := min_le_left _ _
  have hR_le_R_c : R ≤ R_c := min_le_right _ _
  -- Apply the radius-bound planar count.
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, h_count⟩ :=
    localKFoldMultiplicity_preimage_card_with_radius_bound (g := F) (x₀ := z₀)
      (w₀ := F z₀) (k := k) (R := R) hpos hR_pos hF_an rfl hord
  -- ε ≤ R ≤ R_t and ε ≤ R ≤ R_c.
  have hε_le_R_t : ε ≤ R_t := hε_le_R.trans hR_le_R_t
  have hε_le_R_c : ε ≤ R_c := hε_le_R.trans hR_le_R_c
  -- Choose V := source(chartAt(fx)) ∩ chartAt(fx) ⁻¹' ball (F z₀) δ.
  set V : Set Y := (chartAt ℂ (f x)).source ∩
    (chartAt ℂ (f x)) ⁻¹' Metric.ball (F z₀) δ with hV_def
  have h_V_open : IsOpen V := by
    refine (chartAt ℂ (f x)).open_source.inter ?_
    -- (chartAt (f x)) is continuous on its source. A preimage of an open set
    -- under a continuous-on map is the intersection of an open set with the source.
    -- But here V is (source) ∩ (chartAt(fx)⁻¹' ball …). The chart map continuous-on
    -- gives that on source, the preimage of `ball` is open in source. We want it
    -- open in Y. Use:
    --   `ContinuousOn.preimage_isOpen_of_isOpen` would give open in source.
    -- Cleaner: V = (source) ∩ (chartAt(fx))⁻¹' (open ball). The intersection is
    -- open iff each piece is open in Y and the intersection makes sense; but
    -- (chartAt(fx))⁻¹' (open ball) is not necessarily open globally.
    -- The proper form: V is open iff for each y in V, V is a neighborhood. We
    -- show V is open as the intersection: source ∩ (preimage). Use the fact
    -- that on `source`, `chartAt (fx)` is continuous, so the preimage of `ball`
    -- is open in source, hence open in `Y` (since source is open).
    -- Standard step: `(chartAt (f x)).continuousOn` gives `ContinuousOn _ source`.
    -- Restrict: `((chartAt (f x)).continuousOn).isOpen_inter_preimage Met.ball`.
    have hco : ContinuousOn (chartAt ℂ (f x)) (chartAt ℂ (f x)).source :=
      (chartAt ℂ (f x)).continuousOn_toFun
    have := hco.isOpen_inter_preimage (chartAt ℂ (f x)).open_source
      (Metric.isOpen_ball (x := F z₀) (ε := δ))
    -- Refit the shape: `isOpen_inter_preimage` produces
    -- `IsOpen ((source) ∩ chartAt(fx) ⁻¹' (ball))`.
    convert this using 1
  have h_fx_in_V : f x ∈ V := by
    refine ⟨mem_chart_source ℂ (f x), ?_⟩
    show (chartAt ℂ (f x)) (f x) ∈ Metric.ball (F z₀) δ
    rw [hF_z₀_eq]; exact Metric.mem_ball_self hδ_pos
  refine ⟨ε, V, hε_pos, h_V_open, h_fx_in_V, ?_⟩
  -- Main count.
  intro w hw_V hw_ne
  obtain ⟨hw_src, hw_ball⟩ := hw_V
  -- Translate: c := chartAt(fx) w. Then c ∈ ball (F z₀) δ.
  set c : ℂ := (chartAt ℂ (f x)) w with hc_def
  have hc_ball : c ∈ Metric.ball (F z₀) δ := hw_ball
  have hc_ne : c ≠ F z₀ := by
    rw [hc_def, hF_z₀_eq]
    intro hc_eq
    -- chartAt(fx) is injective on source; (fx) ∈ source, w ∈ source.
    have h_inj := (chartAt ℂ (f x)).injOn hw_src (mem_chart_source ℂ (f x)) hc_eq
    exact hw_ne h_inj
  -- Translate the ball-condition from `g x₀` to `F z₀`. Note: `localKFoldMultiplicity_preimage_card_with_radius_bound`
  -- speaks about `Metric.ball (g x₀) δ`. With g = F and x₀ = z₀, the condition is
  -- ball (F z₀) δ. So h_count applies directly.
  have h_planar_count : ({z ∈ Metric.ball z₀ ε | F z = c} : Set ℂ).ncard = k := by
    have : c ∈ Metric.ball (F z₀) δ := hc_ball
    have h_F_z₀_eq_g : F z₀ = F z₀ := rfl
    -- h_count: ∀ w ∈ ball (F z₀) δ, w ≠ F z₀ → ...
    -- Note h_count uses `F` for `g` and `z₀` for `x₀`, so `g x₀ = F z₀`.
    have hc_ne' : c ≠ F z₀ := hc_ne
    have hc_ball' : c ∈ Metric.ball (F z₀) δ := hc_ball
    -- But h_count is stated as `Metric.ball (g x₀) δ` where `g x₀ = F z₀ = w₀`?
    -- We instantiated `w₀ = F z₀` and `h_w₀ : g x₀ = w₀` is `rfl`. So both forms agree.
    exact h_count c hc_ball' hc_ne'
  -- Now lift via the chart bijection. Define
  --   PlanarSet := {z ∈ ball z₀ ε | F z = c}, |PlanarSet| = k.
  --   ManifoldSet := f ⁻¹' {w} ∩ D_x, where D_x = source ∩ chart⁻¹(ball z₀ ε).
  -- Show (chartAt x).symm '' PlanarSet = ManifoldSet via injectivity of symm
  -- on target, then apply ncard_image_of_injOn.
  set Planar : Set ℂ := {z ∈ Metric.ball z₀ ε | F z = c} with hPlanar_def
  set D_x : Set X := (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Metric.ball z₀ ε with hD_def
  set Manifold : Set X := f ⁻¹' {w} ∩ D_x with hMan_def
  -- Step A: ball z₀ ε ⊆ target ∩ symm⁻¹ (open_x).
  have h_ball_sub_target : Metric.ball z₀ ε ⊆ (chartAt ℂ x).target := by
    intro z hz
    have hz_R_t : z ∈ Metric.ball z₀ R_t := Metric.ball_subset_ball hε_le_R_t hz
    exact hR_t_sub hz_R_t
  have h_ball_sub_combined :
      Metric.ball z₀ ε ⊆
        (chartAt ℂ x).target ∩
        (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) := by
    intro z hz
    have hz_R_c : z ∈ Metric.ball z₀ R_c := Metric.ball_subset_ball hε_le_R_c hz
    exact hR_c_sub hz_R_c
  -- Step B: chart-bijection lemma between Planar and Manifold.
  -- Forward: φ.symm '' Planar ⊆ Manifold.
  have h_forward : (chartAt ℂ x).symm '' Planar ⊆ Manifold := by
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
    -- F z = c ⇒ chartAt(fx) (f x') = chartAt(fx) w. Both are in source ⇒ equal.
    have hfx'_eq : f x' = w := by
      have h1 : (chartAt ℂ (f x)) (f x') = (chartAt ℂ (f x)) w := by
        rw [← h_F_z]; rw [hz_F]
      exact (chartAt ℂ (f x)).injOn hf_x'_src hw_src h1
    refine ⟨?_, ?_⟩
    · show f x' ∈ ({w} : Set Y); exact hfx'_eq
    refine ⟨hx'_src, ?_⟩
    show (chartAt ℂ x) x' ∈ Metric.ball z₀ ε
    rw [hx'_chart]; exact hz_ball
  -- Backward: Manifold ⊆ φ.symm '' Planar.
  have h_backward : Manifold ⊆ (chartAt ℂ x).symm '' Planar := by
    rintro x' ⟨hfx', hD⟩
    obtain ⟨hx'_src, hx'_chart_ball⟩ := hD
    have hfx'_w : f x' = w := hfx'
    set z : ℂ := (chartAt ℂ x) x' with hz_def
    have hz_ball : z ∈ Metric.ball z₀ ε := hx'_chart_ball
    have hz_target : z ∈ (chartAt ℂ x).target := h_ball_sub_target hz_ball
    have hz_symm : (chartAt ℂ x).symm z = x' := (chartAt ℂ x).left_inv hx'_src
    have h_F_z : F z = (chartAt ℂ (f x)) (f x') := by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = (chartAt ℂ (f x)) (f x')
      simp [Function.comp, hz_symm]
    have h_F_z_eq_c : F z = c := by rw [h_F_z, hfx'_w, hc_def]
    refine ⟨z, ⟨hz_ball, h_F_z_eq_c⟩, hz_symm⟩
  have h_set_eq : Manifold = (chartAt ℂ x).symm '' Planar :=
    Set.Subset.antisymm h_backward h_forward
  -- Step C: injectivity of symm on Planar (since Planar ⊆ target, where symm is injective).
  have h_injOn : Set.InjOn (chartAt ℂ x).symm Planar := by
    intro a ha b hb hab
    have ha_target : a ∈ (chartAt ℂ x).target := h_ball_sub_target ha.1
    have hb_target : b ∈ (chartAt ℂ x).target := h_ball_sub_target hb.1
    -- (chartAt x).symm is injective on target.
    have ha_eq : (chartAt ℂ x) ((chartAt ℂ x).symm a) = a := (chartAt ℂ x).right_inv ha_target
    have hb_eq : (chartAt ℂ x) ((chartAt ℂ x).symm b) = b := (chartAt ℂ x).right_inv hb_target
    rw [hab] at ha_eq
    exact ha_eq.symm.trans hb_eq
  -- Step D: card transport.
  have h_ncard : Manifold.ncard = Planar.ncard := by
    rw [h_set_eq]
    exact Set.ncard_image_of_injOn h_injOn
  rw [h_ncard, h_planar_count]

end Manifold
end JacobianChallenge

end
