/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticKthRoot
import JacobianChallenge.Manifold.LocalKFoldMultiplicity
import JacobianChallenge.Manifold.LocalMultiplicityInvariance
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional k-fold local multiplicity (composition of ZZ74 + ZZ75 + ZZ87)

Given a local analytic factorization

  `g(z) - w₀ = (z - x₀)^k · u(z)`,    `u` analytic, `u(x₀) ≠ 0`,    `k ≥ 1`,

we compose

* **ZZ87** — `analytic_kth_root_of_nonvanishing` — to get an analytic
  `k`-th root branch `r` of `u` on a small disc.
* **ZZ75** — `KthRootSubstitution` — packaged as the local substitution
  `v(z) := (z - x₀) · r(z)`, with `v(z)^k = g(z) - w₀`, `v(x₀) = 0`,
  `v'(x₀) = r(x₀) ≠ 0`.
* **ZZ74** — `localMultiplicityOne_preimage_card` (re-implemented inline
  here with an extra radius bound) — applied to `v`, giving `k = 1`
  preimage counts for `v(z) = ξ` with `ξ` near `0` and nonzero, in any
  pre-chosen radius `ε ≤ ρ`.

For `w ≠ w₀` near `w₀`, the equation `g(z) = w` is equivalent to
`v(z)^k = w - w₀`. The right-hand side has exactly `k` distinct `k`-th
roots in `ℂ` (since `ℂ` is algebraically closed and `w - w₀ ≠ 0`). For
each root `ξ`, ZZ74 gives a unique preimage `z ∈ ball x₀ ε`. Hence the
preimage set has cardinality exactly `k`.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace JacobianChallenge
namespace Manifold

/-- **Bundle construction from a local factorization.** -/
theorem kthRootSubstitution_of_localFactorization
    {g u : ℂ → ℂ} {x₀ w₀ : ℂ} {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (hu_an : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R))
    (hu_x₀ : u x₀ ≠ 0)
    (hfact : ∀ z ∈ Metric.closedBall x₀ R,
        g z - w₀ = (z - x₀) ^ k * u z) :
    KthRootSubstitution g x₀ w₀ k := by
  obtain ⟨r, ρ', hρ'_pos, hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR hu_an hu_x₀ hk
  refine ⟨⟨fun z => (z - x₀) * r z, ρ', hρ'_pos, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      analyticAt_id.sub analyticAt_const
    have h2 : AnalyticAt ℂ r z := hr_an z hz
    exact h1.mul h2
  · show (x₀ - x₀) * r x₀ = 0
    simp
  · have hx₀_in : x₀ ∈ Metric.closedBall x₀ ρ' := Metric.mem_closedBall_self hρ'_pos.le
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
        deriv (fun z => (z - x₀) * r z) x₀ =
          deriv (fun ζ : ℂ => ζ - x₀) x₀ * r x₀ +
          (x₀ - x₀) * deriv r x₀ := by
      simpa using deriv_mul hsub_diff hr_diff
    have hderiv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have hh : deriv (fun ζ : ℂ => ζ - x₀) x₀
            = deriv (id : ℂ → ℂ) x₀ - deriv (fun _ : ℂ => x₀) x₀ :=
        deriv_sub differentiableAt_id (differentiableAt_const x₀)
      rw [hh]; simp
    rw [hderiv, hderiv_sub, sub_self, zero_mul, add_zero, one_mul]
    exact hr_x₀_ne
  · intro z hz
    have hz_in_R : z ∈ Metric.closedBall x₀ R :=
      (Metric.closedBall_subset_closedBall hρ'_le) hz
    have h1 : g z - w₀ = (z - x₀) ^ k * u z := hfact z hz_in_R
    have h2 : r z ^ k = u z := hr_pow z hz
    rw [h1, ← h2, mul_pow]

/-! ## Strengthened ZZ74 with a radius bound

ZZ74 (`localMultiplicityOne_preimage_card`) proves `card = 1` for some
chosen `ε`. Here we re-do the inverse-function-theorem argument with an
**extra constraint** that the chosen `ε` satisfies `ε ≤ R` for any
preassigned `R > 0`.

This is needed for the cardinality count below: we need `ball x₀ ε ⊆
closedBall x₀ ρ` to invoke the bundle's pointwise relation `g z - w₀ =
v(z)^k`. The unstrengthened ZZ74 produces an `ε` we cannot bound a priori.
-/

private theorem localMultiplicityOne_preimage_card_with_radius
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

/-! ## Cardinality of k-th roots of a nonzero complex number -/

/-- Cardinality of k-th roots of a nonzero complex number is `k`. -/
lemma card_kth_roots_complex {k : ℕ} (hk : 1 ≤ k) {a : ℂ} (ha : a ≠ 0) :
    ({ξ : ℂ | ξ ^ k = a}).ncard = k := by
  classical
  set p : Polynomial ℂ := Polynomial.X ^ k - Polynomial.C a with hp_def
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  have hp_deg : p.natDegree = k := by
    rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C
  have hp_ne_zero : p ≠ 0 := fun h => by
    rw [h] at hp_deg; simp at hp_deg; exact hk0 hp_deg.symm
  have h_roots_eq : ({ξ : ℂ | ξ ^ k = a}) = (p.roots.toFinset : Set ℂ) := by
    ext ξ
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Finset.mem_coe,
               Multiset.mem_toFinset, Polynomial.mem_roots hp_ne_zero,
               Polynomial.IsRoot, hp_def, Polynomial.eval_sub,
               Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
               sub_eq_zero]
  rw [h_roots_eq, Set.ncard_coe_Finset]
  have h_separable : p.Separable := by
    rw [hp_def]
    exact Polynomial.separable_X_pow_sub_C a (by exact_mod_cast hk0) ha
  have h_splits : Polynomial.Splits (RingHom.id ℂ) p :=
    (Complex.isAlgClosed).splits _
  have h_card_roots : p.roots.card = p.natDegree :=
    (Polynomial.splits_iff_card_roots.mp h_splits)
  have h_nodup : p.roots.Nodup := h_separable.squarefree.nodup_roots
  rw [Multiset.toFinset_card_of_nodup h_nodup, h_card_roots, hp_deg]

/-! ## Main count from the bundle -/

/-- **Cardinality count from the substitution bundle.**

If `KthRootSubstitution g x₀ w₀ k` holds with `g x₀ = w₀` and `k ≥ 1`,
there exist `ε, δ > 0` such that for every `w ∈ ball w₀ δ \ {w₀}`,
the preimage `{z ∈ ball x₀ ε | g z = w}` has cardinality exactly `k`. -/
theorem localKFoldMultiplicity_preimage_card_of_substitution
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ}
    (hk : 1 ≤ k)
    (hsub : KthRootSubstitution g x₀ w₀ k)
    (h_w₀ : g x₀ = w₀) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀_eq, hv_d, hv_pow⟩ := hsub.exists_substitution
  have hv_at_x₀ : AnalyticAt ℂ v x₀ :=
    hv_an x₀ (Metric.mem_closedBall_self hρ_pos.le)
  -- ZZ74-with-radius applied to v at x₀, with radius bound ρ.
  obtain ⟨ε, hε_pos, hε_le_ρ, δ₁, hδ₁_pos, hZZ74_v⟩ :=
    localMultiplicityOne_preimage_card_with_radius hv_at_x₀ hv_d hρ_pos
  rw [hv_x₀_eq] at hZZ74_v
  -- δ such that δ < (δ₁/2)^k ⇒ each k-th root of (w - w₀) lies in ball 0 δ₁.
  set δ : ℝ := (δ₁ / 2) ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos (by linarith) k
  refine ⟨ε, hε_pos, δ, hδ_pos, ?_⟩
  intro w hw_ball hw_ne
  set w₁ : ℂ := w - w₀ with hw₁_def
  have hw₀_eq : w₀ = g x₀ := h_w₀.symm
  have hw₁_ne : w₁ ≠ 0 := by
    rw [hw₁_def, sub_ne_zero, hw₀_eq]; exact hw_ne
  have hw_dist : ‖w - w₀‖ < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hw_ball
    rw [← hw₀_eq]; exact hw_ball
  -- Bound on each k-th root.
  have h_roots_small : ∀ ξ : ℂ, ξ ^ k = w₁ → ‖ξ‖ < δ₁ := by
    intro ξ hξ
    have hξn : ‖ξ‖ ^ k = ‖w₁‖ := by rw [← hξ]; exact norm_pow ξ k
    have h1 : ‖ξ‖ ^ k < (δ₁ / 2) ^ k := by
      rw [hξn]; exact lt_of_lt_of_le hw_dist (le_of_eq hδ_def)
    have hξ_nn : 0 ≤ ‖ξ‖ := norm_nonneg _
    have hδ₁_half_nn : 0 ≤ δ₁ / 2 := by linarith
    have h2 : ‖ξ‖ < δ₁ / 2 := by
      by_contra h
      push_neg at h
      have hh : (δ₁ / 2) ^ k ≤ ‖ξ‖ ^ k := pow_le_pow_left hδ₁_half_nn h k
      linarith
    linarith
  have h_roots_ne : ∀ ξ : ℂ, ξ ^ k = w₁ → ξ ≠ 0 := by
    intro ξ hξ hξ0
    rw [hξ0] at hξ
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    rw [zero_pow hk0] at hξ
    exact hw₁_ne hξ.symm
  -- For each k-th root ξ, ZZ74 gives unique preimage in ball x₀ ε.
  have hv_count : ∀ ξ : ℂ, ξ ^ k = w₁ →
      ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξ
    have hξ_norm : ‖ξ‖ < δ₁ := h_roots_small ξ hξ
    have hξ_ne : ξ ≠ 0 := h_roots_ne ξ hξ
    have hξ_ball : ξ ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hξ_norm
    exact hZZ74_v ξ hξ_ball hξ_ne
  -- Set equality: g-preimage = union over k-th roots ξ of v-preimages-at-ξ.
  have h_ball_sub_closed : Metric.ball x₀ ε ⊆ Metric.closedBall x₀ ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    exact (le_of_lt hz).trans hε_le_ρ
  have h_pre_eq :
      {z ∈ Metric.ball x₀ ε | g z = w}
        = ⋃ ξ ∈ {ξ : ℂ | ξ ^ k = w₁}, {z ∈ Metric.ball x₀ ε | v z = ξ} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz_ball, hz_g⟩
      refine ⟨v z, ?_, hz_ball, rfl⟩
      have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball
      have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
      rw [hz_g] at hpow
      -- w - w₀ = v z ^ k, so v z ^ k = w₁.
      show v z ^ k = w₁
      rw [hw₁_def]; exact hpow.symm
    · rintro ⟨ξ, hξ, hz_ball, hvz⟩
      refine ⟨hz_ball, ?_⟩
      have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball
      have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
      rw [hvz] at hpow
      -- g z - w₀ = ξ^k = w₁ = w - w₀, so g z = w.
      have : g z = ξ ^ k + w₀ := by linear_combination hpow
      rw [this, hξ]
      show w₁ + w₀ = w
      rw [hw₁_def]; ring
  rw [h_pre_eq]
  -- Now compute cardinality of the union. The k-th roots set has card k.
  -- Each fiber {z ∈ ball x₀ ε | v z = ξ} has card 1 for ξ a k-th root of w₁.
  -- The fibers are pairwise disjoint (different v z values).
  -- So total card = sum of 1's over k-th roots = k.
  classical
  -- Use the bijection: preimage set ≃ k-th roots set via z ↦ v z.
  -- We package this as ncard of a sigma-style decomposition.
  set Roots : Set ℂ := {ξ : ℂ | ξ ^ k = w₁} with hRoots_def
  have hRoots_card : Roots.ncard = k := card_kth_roots_complex hk hw₁_ne
  have hRoots_finite : Roots.Finite := by
    rw [Set.Finite]
    exact Set.finite_of_ncard_ne_zero (by rw [hRoots_card]; exact Nat.one_le_iff_ne_zero.mp hk)
  -- Disjointness on indexing.
  have h_disj : ∀ ξ ∈ Roots, ∀ η ∈ Roots, ξ ≠ η →
      Disjoint ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ)
               {z ∈ Metric.ball x₀ ε | v z = η} := by
    intro ξ _ η _ hne
    rw [Set.disjoint_iff_inter_eq_empty]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, hξ⟩, ⟨_, hη⟩⟩
    exact hne (hξ.trans hη.symm)
  -- ncard of disjoint union over a finite indexing is sum of ncards.
  have h_ncard_union :
      (⋃ ξ ∈ Roots, ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ)).ncard
        = ∑ᶠ ξ ∈ Roots, ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard := by
    apply Set.ncard_biUnion (s := Roots) (t := fun ξ => {z ∈ Metric.ball x₀ ε | v z = ξ})
    · exact hRoots_finite
    · intro ξ hξ
      have h1 : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := hv_count ξ hξ
      exact Set.finite_of_ncard_eq_succ h1
    · exact h_disj
  rw [h_ncard_union]
  -- Each summand is 1; finsum over Roots equals card Roots.
  have h_each : ∀ ξ ∈ Roots, ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξ; exact hv_count ξ hξ
  have h_sum :
      (∑ᶠ ξ ∈ Roots, ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard)
        = ∑ᶠ _ ∈ Roots, (1 : ℕ) := by
    refine finsum_mem_congr rfl ?_
    intro ξ hξ; exact h_each ξ hξ
  rw [h_sum]
  rw [finsum_mem_one]
  exact hRoots_card

/-! ## End-to-end unconditional theorem -/

/-- **Unconditional `k`-fold local multiplicity** (composition of
ZZ74 + ZZ75 + ZZ87).

Given:
* `g : ℂ → ℂ` analytic (of type witnessed only via the factorization),
* `g x₀ = w₀`,
* a local factorization `g(z) - w₀ = (z - x₀)^k · u(z)` on
  `closedBall x₀ R`, with `u` analytic there and `u(x₀) ≠ 0`,
* `k ≥ 1`,

there exist `ε, δ > 0` such that for every `w ∈ ball w₀ δ \ {w₀}`,
the equation `g z = w` has **exactly `k`** solutions in `ball x₀ ε`. -/
theorem localKFoldMultiplicity_preimage_card_unconditional
    {g u : ℂ → ℂ} {x₀ w₀ : ℂ} {R : ℝ} {k : ℕ}
    (hR : 0 < R) (hk : 1 ≤ k)
    (hu_an : AnalyticOnNhd ℂ u (Metric.closedBall x₀ R))
    (hu_x₀ : u x₀ ≠ 0)
    (h_w₀ : g x₀ = w₀)
    (hfact : ∀ z ∈ Metric.closedBall x₀ R,
        g z - w₀ = (z - x₀) ^ k * u z) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  have hsub : KthRootSubstitution g x₀ w₀ k :=
    kthRootSubstitution_of_localFactorization hR hk hu_an hu_x₀ hfact
  exact localKFoldMultiplicity_preimage_card_of_substitution hk hsub h_w₀

end Manifold
end JacobianChallenge

end
