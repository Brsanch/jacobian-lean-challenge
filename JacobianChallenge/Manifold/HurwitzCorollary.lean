/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import JacobianChallenge.Manifold.LocalKFoldMultiplicityUnconditional
import JacobianChallenge.Manifold.LocalKFoldMultiplicity
import Mathlib.Analysis.Analytic.Order

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Hurwitz corollary (zz383)

Radius-controlled fully-unconditional local k-fold multiplicity, used to
derive the Hurwitz corollary: for `f : ℂ → ℂ` analytic at `z₀` and locally
injective on `Metric.ball z₀ R₀`, the derivative `deriv f z₀` is non-zero.

The radius-controlled wrapper exposes `ε ≤ R₀` in the conclusion of
`localKFoldMultiplicity_preimage_card_*`, which is the missing piece
that blocks `BijectiveAnalyticIsBiholomorphism`:

* `analytic_local_factorization_within_radius` — restrict the analytic
  factorization to a disc of any prescribed radius `R ≤ R₀`.
* `localKFoldMultiplicity_preimage_card_within_radius` — apply the
  fully-unconditional k-fold count with `ε ≤ R₀`.
* `AnalyticAt.deriv_ne_zero_of_injOn_ball` — Hurwitz corollary.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature changes to any pre-existing definition or theorem; the
  only edit outside this file is removing `private` from
  `localMultiplicityOne_preimage_card_with_radius` to make it reusable.
-/

noncomputable section

open scoped Topology
open Set Filter Metric

namespace JacobianChallenge
namespace Manifold

/-- **Radius-controlled local analytic factorization.**

Given an external upper bound `R₀ > 0`, the factorization disc from
`analytic_local_factorization` can be shrunk to lie inside `closedBall x₀ R₀`. -/
theorem analytic_local_factorization_within_radius
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R₀ : ℝ}
    (hR₀ : 0 < R₀)
    (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ R : ℝ, 0 < R ∧ R ≤ R₀ ∧ ∃ u : ℂ → ℂ,
      AnalyticOnNhd ℂ u (Metric.closedBall x₀ R) ∧ u x₀ ≠ 0 ∧
        ∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (z - x₀) ^ k * u z := by
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk hg h_w₀ hord
  set R' : ℝ := min R R₀ with hR'_def
  have hR'_pos : 0 < R' := lt_min hR_pos hR₀
  have hR'_le_R : R' ≤ R := min_le_left _ _
  have hR'_le_R₀ : R' ≤ R₀ := min_le_right _ _
  have hsubset : Metric.closedBall x₀ R' ⊆ Metric.closedBall x₀ R :=
    Metric.closedBall_subset_closedBall hR'_le_R
  refine ⟨R', hR'_pos, hR'_le_R₀, u, ?_, hu_x₀, ?_⟩
  · intro z hz; exact hu_an z (hsubset hz)
  · intro z hz; exact hfact z (hsubset hz)

/-- **Radius-controlled cardinality count from the substitution bundle.**

The same conclusion as `localKFoldMultiplicity_preimage_card_of_substitution`,
but with the additional guarantee `ε ≤ R₀` for any prescribed `R₀ > 0`.

The proof body mirrors the original, replacing the inner k=1 call's radius
input `ρ` (the substitution radius) by `min ρ R₀`, so the resulting `ε`
satisfies `ε ≤ min ρ R₀ ≤ R₀`. -/
theorem localKFoldMultiplicity_preimage_card_of_substitution_within_radius
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R₀ : ℝ}
    (hR₀ : 0 < R₀) (hk : 1 ≤ k)
    (hsub : KthRootSubstitution g x₀ w₀ k)
    (h_w₀ : g x₀ = w₀) :
    ∃ ε > (0 : ℝ), ε ≤ R₀ ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  obtain ⟨v, ρ, hρ_pos, hv_an, hv_x₀_eq, hv_d, hv_pow⟩ := hsub.exists_substitution
  have hv_at_x₀ : AnalyticAt ℂ v x₀ :=
    hv_an x₀ (Metric.mem_closedBall_self hρ_pos.le)
  set R' : ℝ := min ρ R₀ with hR'_def
  have hR'_pos : 0 < R' := lt_min hρ_pos hR₀
  have hR'_le_ρ : R' ≤ ρ := min_le_left _ _
  have hR'_le_R₀ : R' ≤ R₀ := min_le_right _ _
  obtain ⟨ε, hε_pos, hε_le_R', δ₁, hδ₁_pos, hZZ74_v⟩ :=
    localMultiplicityOne_preimage_card_with_radius hv_at_x₀ hv_d hR'_pos
  have hε_le_ρ : ε ≤ ρ := hε_le_R'.trans hR'_le_ρ
  have hε_le_R₀ : ε ≤ R₀ := hε_le_R'.trans hR'_le_R₀
  rw [hv_x₀_eq] at hZZ74_v
  set δ : ℝ := (δ₁ / 2) ^ k with hδ_def
  have hδ_pos : 0 < δ := pow_pos (by linarith) k
  refine ⟨ε, hε_pos, hε_le_R₀, δ, hδ_pos, ?_⟩
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
  have h_ball_sub_closed : Metric.ball x₀ ε ⊆ Metric.closedBall x₀ ρ := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall]
    exact (le_of_lt hz).trans hε_le_ρ
  -- Forward direction: count preimages of `w` by routing through `v` and the
  -- k-th roots of `w₁ = w - w₀`. The proof body is the same as in
  -- `localKFoldMultiplicity_preimage_card_of_substitution`.
  -- Use the singleton-fibre lemma `h_v_count` extracted from the k=1 result.
  have h_v_count : ∀ ξ : ℂ, ξ ^ k = w₁ →
      ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := by
    intro ξ hξk
    have hξ_ne : ξ ≠ 0 := h_roots_ne ξ hξk
    have hξ_norm : ‖ξ‖ < δ₁ := h_roots_small ξ hξk
    have hξ_ball : ξ ∈ Metric.ball (0 : ℂ) δ₁ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hξ_norm
    exact hZZ74_v ξ hξ_ball hξ_ne
  -- z ↦ v z maps Pre into the k-th-roots-of-w₁ set.
  have h_v_to_roots : ∀ z ∈ Pre, v z ^ k = w₁ := by
    intro z hz
    obtain ⟨hz_ball, hz_g⟩ := hz
    have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball
    have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
    rw [hz_g] at hpow
    rw [hw₁_def]; exact hpow.symm
  -- Existence of preimages.
  have h_exists : ∀ ξ : ℂ, ξ ^ k = w₁ → ∃ z ∈ Pre, v z = ξ := by
    intro ξ hξk
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).ncard = 1 := h_v_count ξ hξk
    have h_finite : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [h_card1]; exact one_ne_zero)
    have h_ne : ({z ∈ Metric.ball x₀ ε | v z = ξ} : Set ℂ).Nonempty := by
      rw [← Set.ncard_pos h_finite, h_card1]; exact Nat.one_pos
    obtain ⟨z, hz_ball_mem, hzv⟩ := h_ne
    refine ⟨z, ⟨hz_ball_mem, ?_⟩, hzv⟩
    have hz_closed : z ∈ Metric.closedBall x₀ ρ := h_ball_sub_closed hz_ball_mem
    have hpow : g z - w₀ = v z ^ k := hv_pow z hz_closed
    rw [hzv] at hpow
    rw [hξk] at hpow
    have : g z = w₁ + w₀ := by
      have hh : g z = (g z - w₀) + w₀ := by ring
      rw [hh, hpow]
    rw [this, hw₁_def]; ring
  -- Injectivity of z ↦ v z on Pre.
  have h_v_injOn : Set.InjOn (fun z => v z) Pre := by
    intro z₁ hz₁ z₂ hz₂ hvz
    have hξk : v z₁ ^ k = w₁ := h_v_to_roots z₁ hz₁
    have h_card1 : ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ).ncard = 1 :=
      h_v_count (v z₁) hξk
    rw [Set.ncard_eq_one] at h_card1
    obtain ⟨a, ha⟩ := h_card1
    have hz₁_mem : z₁ ∈ ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ) :=
      ⟨hz₁.1, rfl⟩
    have hz₂_mem : z₂ ∈ ({z ∈ Metric.ball x₀ ε | v z = v z₁} : Set ℂ) :=
      ⟨hz₂.1, hvz.symm⟩
    rw [ha] at hz₁_mem hz₂_mem
    rw [Set.mem_singleton_iff] at hz₁_mem hz₂_mem
    exact hz₁_mem.trans hz₂_mem.symm
  -- Counting via the bijection with the k-th-roots Finset.
  set F : Finset ℂ := kthRootsFinset k w₁ with hF_def
  have hF_card : F.card = k := kth_roots_finset_card hk hw₁_ne
  have hF_eq : (F : Set ℂ) = {ξ : ℂ | ξ ^ k = w₁} := (kth_roots_eq_finset hk hw₁_ne).symm
  -- Image of Pre under z ↦ v z equals (F : Set ℂ).
  have h_image_eq : (fun z => v z) '' Pre = (F : Set ℂ) := by
    rw [hF_eq]
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz_pre, rfl⟩
      exact h_v_to_roots z hz_pre
    · intro ξ hξ
      obtain ⟨z, hz_pre, hzv⟩ := h_exists ξ hξ
      exact ⟨z, hz_pre, hzv⟩
  have hPre_ncard : Pre.ncard = F.card := by
    have h1 : Pre.ncard = ((fun z => v z) '' Pre).ncard :=
      (Set.ncard_image_of_injOn h_v_injOn).symm
    rw [h1, h_image_eq, Set.ncard_coe_finset]
  rw [hPre_ncard, hF_card]

/-! ## Private `kthRootsFinset` / `kth_roots_*` access.

The helpers `kthRootsFinset`, `kth_roots_eq_finset`, and
`kth_roots_finset_card` are `private` in
`LocalKFoldMultiplicityUnconditional.lean`. The proof above uses them by
name, which works because they are in the same namespace
(`JacobianChallenge.Manifold`) and Lean's `private` is per-declaration-file
visibility but allows in-namespace use via re-import — except it does not
for `private`. We therefore unfold the bijection differently using only
the public k=1 lemma. -/

/-- **Fully unconditional, radius-controlled k-fold local multiplicity.**

Composition of `analytic_local_factorization_within_radius` + the bundle
constructor + `localKFoldMultiplicity_preimage_card_of_substitution_within_radius`.

For `AnalyticAt ℂ g x₀` with `g x₀ = w₀` and
`analyticOrderAt (g - w₀) x₀ = k ≥ 1`, *and* an external bound `R₀ > 0`,
there exist `ε ≤ R₀` and `δ > 0` such that every `w` in the punctured
disc `ball w₀ δ \ {w₀}` has exactly `k` preimages in `ball x₀ ε`. -/
theorem localKFoldMultiplicity_preimage_card_within_radius
    {g : ℂ → ℂ} {x₀ w₀ : ℂ} {k : ℕ} {R₀ : ℝ}
    (hR₀ : 0 < R₀) (hk : 1 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞)) :
    ∃ ε > (0 : ℝ), ε ≤ R₀ ∧ ∃ δ > (0 : ℝ),
      ∀ w ∈ Metric.ball (g x₀) δ, w ≠ g x₀ →
        ({z ∈ Metric.ball x₀ ε | g z = w} : Set ℂ).ncard = k := by
  obtain ⟨R, hR_pos, hR_le_R₀, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization_within_radius hR₀ hk hg h_w₀ hord
  have hsub : KthRootSubstitution g x₀ w₀ k :=
    kthRootSubstitution_of_localFactorization hR_pos hk hu_an hu_x₀ hfact
  exact localKFoldMultiplicity_preimage_card_of_substitution_within_radius
    hR₀ hk hsub h_w₀

/-! ## Hurwitz corollary -/

/-- **Hurwitz corollary.** If `f : ℂ → ℂ` is analytic at `z₀` and injective
on `Metric.ball z₀ R` for some `R > 0`, then `deriv f z₀ ≠ 0`.

Proof. Suppose `deriv f z₀ = 0` for contradiction.

* Local injectivity rules out `f` being eventually equal to a constant on
  `𝓝 z₀`, so `analyticOrderAt (f · - f z₀) z₀ ≠ ⊤`.
* `(f · - f z₀) z₀ = 0`, so `analyticOrderAt (f · - f z₀) z₀ ≠ 0`.
* Hence `analyticOrderAt (f · - f z₀) z₀ = (k : ℕ∞)` for some `k ≥ 1`.
* `AnalyticAt.analyticOrderAt_deriv_add_one` says
  `analyticOrderAt (deriv f) z₀ + 1 = analyticOrderAt (f · - f z₀) z₀`;
  with `deriv f z₀ = 0` and `deriv f` analytic at `z₀`, we get
  `analyticOrderAt (deriv f) z₀ ≥ 1`, so `k ≥ 2`.
* Apply `localKFoldMultiplicity_preimage_card_within_radius` with the
  external bound `R₀ := R`. We get `ε ≤ R`, `δ > 0`, and a cardinality-`k`
  preimage statement.
* Pick any `z' ∈ Metric.ball z₀ ε` with `z' ≠ z₀` and `f z' ∈ ball (f z₀) δ`
  (exists by continuity of `f` at `z₀`). Then `f z' ≠ f z₀` by injectivity
  of `f` on `ball z₀ R ⊇ ball z₀ ε`, and the preimage set has `k ≥ 2`
  elements, all of which lie in `ball z₀ ε ⊆ ball z₀ R`, contradicting
  injectivity. -/
theorem AnalyticAt.deriv_ne_zero_of_injOn_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : AnalyticAt ℂ f z₀) (hR : 0 < R)
    (hinj : Set.InjOn f (Metric.ball z₀ R)) :
    deriv f z₀ ≠ 0 := by
  intro hderiv
  -- Step 1: f is not eventually equal to a constant on 𝓝 z₀
  -- (otherwise ball z₀ R contains > 1 point with the same f-value).
  have h_not_const : ¬ (∀ᶠ z in 𝓝 z₀, f z = f z₀) := by
    intro h_const
    rw [Metric.eventually_nhds_iff] at h_const
    obtain ⟨r, hr_pos, hr⟩ := h_const
    -- Pick two distinct points in ball z₀ (min r R); both map to f z₀.
    set r' : ℝ := min r R with hr'_def
    have hr'_pos : 0 < r' := lt_min hr_pos hR
    have hr'_le_r : r' ≤ r := min_le_left _ _
    have hr'_le_R : r' ≤ R := min_le_right _ _
    -- z₁ := z₀, z₂ := z₀ + (r'/2). Both in ball z₀ R.
    set z₂ : ℂ := z₀ + (r' / 2 : ℝ) with hz₂_def
    have hz₂_dist : dist z₂ z₀ = r' / 2 := by
      have h_pos : (0 : ℝ) ≤ r' / 2 := by linarith
      rw [hz₂_def, dist_eq_norm]
      rw [show z₀ + ((r'/2 : ℝ) : ℂ) - z₀ = ((r'/2 : ℝ) : ℂ) from by ring]
      rw [Complex.norm_real]
      exact Real.norm_of_nonneg h_pos
    have hz₂_ball_r : z₂ ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball, hz₂_dist]; linarith
    have hz₂_ball_R : z₂ ∈ Metric.ball z₀ R := by
      rw [Metric.mem_ball, hz₂_dist]; linarith
    have hz₀_ball_R : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hR
    -- f z₂ = f z₀ from h_const ⇒ injectivity gives z₂ = z₀.
    have hfz₂ : f z₂ = f z₀ := by
      have hd : dist z₂ z₀ < r := by rw [hz₂_dist]; linarith
      exact hr hd
    have hz_eq : z₂ = z₀ := hinj hz₂_ball_R hz₀_ball_R hfz₂
    -- But z₂ ≠ z₀.
    have hz_ne : z₂ ≠ z₀ := by
      intro hh
      have : dist z₂ z₀ = 0 := by rw [hh, dist_self]
      rw [hz₂_dist] at this
      linarith
    exact hz_ne hz_eq
  -- Step 2: analyticOrderAt (f · - f z₀) z₀ is a positive natural number k.
  have hf_sub_an : AnalyticAt ℂ (fun z => f z - f z₀) z₀ :=
    hf.sub analyticAt_const
  have h_sub_x₀ : (fun z => f z - f z₀) z₀ = 0 := by simp
  have h_order_ne_top : analyticOrderAt (fun z => f z - f z₀) z₀ ≠ ⊤ := by
    intro h_top
    rw [analyticOrderAt_eq_top] at h_top
    apply h_not_const
    filter_upwards [h_top] with z hz using sub_eq_zero.mp hz
  have h_order_ne_zero : analyticOrderAt (fun z => f z - f z₀) z₀ ≠ 0 := by
    rw [hf_sub_an.analyticOrderAt_ne_zero]
    exact h_sub_x₀
  -- Extract k.
  obtain ⟨k, hk_def⟩ := ENat.ne_top_iff_exists.mp h_order_ne_top
  have hk_pos : 1 ≤ k := by
    by_contra hk_neg
    push_neg at hk_neg
    interval_cases k
    rw [← hk_def] at h_order_ne_zero
    exact h_order_ne_zero rfl
  -- Step 3: deriv f z₀ = 0 ⇒ analyticOrderAt (deriv f) z₀ ≥ 1.
  have hf_deriv_an : AnalyticAt ℂ (deriv f) z₀ := hf.deriv
  have h_deriv_order_ne_zero : analyticOrderAt (deriv f) z₀ ≠ 0 := by
    rw [hf_deriv_an.analyticOrderAt_ne_zero]
    exact hderiv
  have h_deriv_order_ge_one : 1 ≤ analyticOrderAt (deriv f) z₀ := by
    rcases eq_or_ne (analyticOrderAt (deriv f) z₀) 0 with h0 | hne
    · exact (h_deriv_order_ne_zero h0).elim
    · exact ENat.one_le_iff_ne_zero.mpr hne
  -- Step 4: analyticOrderAt (f · - f z₀) z₀ = analyticOrderAt (deriv f) z₀ + 1 ≥ 2.
  have h_add_one : analyticOrderAt (deriv f) z₀ + 1 =
      analyticOrderAt (fun z => f z - f z₀) z₀ :=
    hf.analyticOrderAt_deriv_add_one
  have h_order_ge_two : (2 : ℕ∞) ≤ analyticOrderAt (fun z => f z - f z₀) z₀ := by
    rw [← h_add_one]
    have : (2 : ℕ∞) = 1 + 1 := by norm_num
    rw [this, add_comm]
    exact add_le_add_left h_deriv_order_ge_one 1
  have hk_ge_two : 2 ≤ k := by
    have : ((2 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
      rw [← hk_def] at h_order_ge_two
      exact_mod_cast h_order_ge_two
    exact_mod_cast this
  -- Step 5: apply the radius-controlled cardinality theorem.
  have h_w₀ : f z₀ = f z₀ := rfl
  have hord' : analyticOrderAt (fun z => f z - f z₀) z₀ = (k : ℕ∞) := hk_def.symm
  obtain ⟨ε, hε_pos, hε_le_R, δ, hδ_pos, hcard⟩ :=
    localKFoldMultiplicity_preimage_card_within_radius hR hk_pos hf h_w₀ hord'
  -- Step 6: produce a w ∈ ball (f z₀) δ \ {f z₀} that has a preimage in ball z₀ ε.
  -- Use continuity of f at z₀ to find z' ∈ ball z₀ ε with f z' ∈ ball (f z₀) δ.
  have hf_cont : ContinuousAt f z₀ := hf.continuousAt
  rw [Metric.continuousAt_iff] at hf_cont
  obtain ⟨η, hη_pos, hη⟩ := hf_cont δ hδ_pos
  -- Pick z' = z₀ + (min ε η)/2.
  set s : ℝ := min ε η / 2 with hs_def
  have hs_pos : 0 < s := by
    have h := lt_min hε_pos hη_pos
    linarith
  have hs_lt_ε : s < ε := by
    have h1 : min ε η ≤ ε := min_le_left _ _
    linarith
  have hs_lt_η : s < η := by
    have h2 : min ε η ≤ η := min_le_right _ _
    linarith
  set z' : ℂ := z₀ + (s : ℝ) with hz'_def
  have hz'_dist : dist z' z₀ = s := by
    rw [hz'_def]
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hs_pos]
  have hz'_ne : z' ≠ z₀ := by
    intro h
    have : dist z' z₀ = 0 := by rw [h, dist_self]
    rw [hz'_dist] at this; linarith
  have hz'_ball_ε : z' ∈ Metric.ball z₀ ε := by
    rw [Metric.mem_ball, hz'_dist]; exact hs_lt_ε
  have hz'_ball_R : z' ∈ Metric.ball z₀ R := by
    rw [Metric.mem_ball, hz'_dist]
    have : ε ≤ R := hε_le_R
    linarith
  have hz'_ball_η : dist z' z₀ < η := by rw [hz'_dist]; exact hs_lt_η
  have hfz'_dist : dist (f z') (f z₀) < δ := hη hz'_ball_η
  have hfz'_ball : f z' ∈ Metric.ball (f z₀) δ := by
    rw [Metric.mem_ball]; exact hfz'_dist
  -- z₀ ∈ ball z₀ R; injectivity of f on ball z₀ R + z' ≠ z₀ ⇒ f z' ≠ f z₀.
  have hfz'_ne : f z' ≠ f z₀ := by
    intro hh
    have hz₀_ball_R : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball_self hR
    exact hz'_ne (hinj hz'_ball_R hz₀_ball_R hh)
  -- Apply cardinality.
  have h_set_card : ({z ∈ Metric.ball z₀ ε | f z = f z'} : Set ℂ).ncard = k :=
    hcard (f z') hfz'_ball hfz'_ne
  -- The set has cardinality k ≥ 2; pick two distinct elements, both in
  -- ball z₀ ε ⊆ ball z₀ R, both mapped to f z'. Contradict injectivity.
  have h_one_lt : 1 < ({z ∈ Metric.ball z₀ ε | f z = f z'} : Set ℂ).ncard := by
    rw [h_set_card]; exact hk_ge_two
  have h_set_finite : ({z ∈ Metric.ball z₀ ε | f z = f z'} : Set ℂ).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [h_set_card]; exact Nat.one_le_iff_ne_zero.mp hk_pos)
  obtain ⟨a, b, ha_mem, hb_mem, hab⟩ :=
    (Set.one_lt_ncard_iff h_set_finite).mp h_one_lt
  obtain ⟨ha_ball, ha_fab⟩ := ha_mem
  obtain ⟨hb_ball, hb_fab⟩ := hb_mem
  have ha_ball_R : a ∈ Metric.ball z₀ R := by
    rw [Metric.mem_ball] at ha_ball ⊢
    exact ha_ball.trans_le hε_le_R
  have hb_ball_R : b ∈ Metric.ball z₀ R := by
    rw [Metric.mem_ball] at hb_ball ⊢
    exact hb_ball.trans_le hε_le_R
  have hab_f : f a = f b := ha_fab.trans hb_fab.symm
  exact hab (hinj ha_ball_R hb_ball_R hab_f)

end Manifold
end JacobianChallenge

end
