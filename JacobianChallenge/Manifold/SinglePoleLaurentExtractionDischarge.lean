/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import JacobianChallenge.Manifold.MultiPoleLaurentExistence

/-! # Discharge of `SinglePoleLaurentExtraction` (ZZ68)

ZZ66 (`MultiPoleLaurentExistence`) introduced the named Prop
`SinglePoleLaurentExtraction g x ε`, which packages the per-pole content
needed by the multi-pole assembly: at a finite-order pole `x` of `g`, on
some open neighbourhood of `closedBall x ε`, `g` decomposes as a finite
principal part plus a local analytic remainder.

This file discharges that Prop **unconditionally** (no `axiom`, no
`sorry`) under the natural hypothesis that `g` is meromorphic at `x`
with finite order (`meromorphicOrderAt g x ≠ ⊤`).

## Headline result

`singlePole_laurent_extraction_of_meromorphicAt`:
for `g : ℂ → ℂ` meromorphic at `x` with finite order, there exists
`ε > 0` such that `SinglePoleLaurentExtraction g x ε` holds.

## Proof strategy

1. `MeromorphicAt.meromorphicOrderAt_eq_int_iff` from mathlib gives an
   analytic factor `G` with `G x ≠ 0` and `g z = (z-x)^n • G z`
   eventually on `𝓝[≠] x`, where `n = meromorphicOrderAt g x : ℤ`.

2. Set `N := (-n).toNat` (number of principal-part terms; `0` in the
   removable / zero case).

3. Apply `AnalyticAt.exists_eq_sum_add_pow_mul` to `G̃(w) := G(w + x)`
   at order `N`, giving global Taylor coefficients
   `c i = iteratedDeriv i G̃ 0 / i!` and an analytic-at-0 remainder
   `F : ℂ → ℂ` with
   `G(w + x) = ∑_{i<N} c_i · w^i + w^N · F w`.

4. `AnalyticAt.exists_ball_analyticOnNhd` extracts a positive radius
   `δ > 0` on which `F` is analytic everywhere, and the eventually-eq
   from step 1 gives a radius `r₀ > 0` on which the meromorphic
   factorisation holds for `z ≠ x`.

5. Algebra on the punctured disk: substituting the Taylor expansion
   into `g z = (z-x)^n • G z` and re-indexing `k := N - i` for
   `i ∈ range N` gives
   `g z = (z-x)^{n+N} F(z-x) + ∑_{k=1..N} c_{N-k} · (z-x)^{n+N-k}`.
   Since `n + N = max(n, 0) ≥ 0` (and `= 0` exactly when `n ≤ 0`), the
   power `(z-x)^{n+N-k}` for `k ∈ [1,N]` matches `(z-x)^{-k}` exactly
   when `n ≤ 0`, i.e. in the genuine-pole or order-zero case. In the
   `n > 0` (zero of `g` at `x`) case, `N = 0` and the sum is empty.

To avoid case-splitting, we package the result as: define `a_k :=
c_{N-k}` if `n + N = 0` (genuinely a pole or order zero), and `0`
otherwise. The remainder `h_x z := (z-x)^{n+N} • F(z-x)` is analytic
on `ball x r` for some `r > 0`.

## Anti-cheat

* No `axiom`, no `sorry`. Only mathlib lemmas + algebra.
* No signature of any pre-existing Prop is changed.
* The named Prop's `∃` content is fully constructed.
-/

noncomputable section

open Complex Set Metric Filter Topology

namespace JacobianChallenge

namespace MultiPoleLaurentExistence

/-- **Discharge of `SinglePoleLaurentExtraction`.**

If `g` is meromorphic at `x` with finite order
(`meromorphicOrderAt g x ≠ ⊤`), then for some `ε > 0`,
`SinglePoleLaurentExtraction g x ε` holds. -/
theorem singlePole_laurent_extraction_of_meromorphicAt
    {g : ℂ → ℂ} {x : ℂ}
    (hg : MeromorphicAt g x)
    (hOrd : meromorphicOrderAt g x ≠ ⊤) :
    ∃ ε : ℝ, 0 < ε ∧ SinglePoleLaurentExtraction g x ε := by
  classical
  -- Step 1. Extract the integer order `n : ℤ` and the analytic factor `G`.
  obtain ⟨n, hn⟩ : ∃ n : ℤ, meromorphicOrderAt g x = n := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hOrd
    exact ⟨m, hm.symm⟩
  obtain ⟨G, hG_an, _hG_ne, hG_eq⟩ :=
    (meromorphicOrderAt_eq_int_iff hg).mp hn
  -- Step 2. Set `N : ℕ` so the principal part has at most `N` terms.
  set N : ℕ := (-n).toNat with hN_def
  -- Step 3. Shift `G` to the origin and apply the global Taylor formula at order `N`.
  have hG_an_shift : AnalyticAt ℂ (fun w : ℂ => G (w + x)) 0 := by
    have h_id : AnalyticAt ℂ (fun w : ℂ => w + x) 0 :=
      (analyticAt_id (𝕜 := ℂ) (x := (0 : ℂ))).add analyticAt_const
    exact hG_an.comp_of_eq h_id (by simp)
  obtain ⟨F, hF_an, hF_eq⟩ := hG_an_shift.exists_eq_sum_add_pow_mul N
  -- Taylor coefficients of the shifted analytic factor.
  set c : ℕ → ℂ := fun i =>
    iteratedDeriv i (fun w : ℂ => G (w + x)) 0 / (i.factorial : ℂ) with hc_def
  have hF_eq' : ∀ w : ℂ,
      G (w + x) = (∑ i ∈ Finset.range N, w ^ i • c i) + w ^ N • F w := by
    intro w
    have h := hF_eq w
    have h_rewrite_term :
        ∀ i : ℕ,
          (w ^ i / (i.factorial : ℂ)) • iteratedDeriv i (fun w : ℂ => G (w + x)) 0
            = w ^ i • c i := by
      intro i
      simp only [hc_def, smul_eq_mul]
      ring
    rw [h]
    congr 1
    exact Finset.sum_congr rfl fun i _ => h_rewrite_term i
  -- Step 4. Get a positive radius for `F` analyticity and for the meromorphic
  -- factorisation `g z = (z-x)^n • G z` (for `z ≠ x`).
  obtain ⟨δ, hδ_pos, hF_anOn⟩ := hF_an.exists_ball_analyticOnNhd
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hG_eq
  obtain ⟨r₀, hr₀_pos, hG_eq_ball⟩ := hG_eq
  set r : ℝ := min δ r₀ with hr_def
  have hr_pos : 0 < r := lt_min hδ_pos hr₀_pos
  refine ⟨r / 2, by linarith, ?_⟩
  -- Step 5. Build the witness for `SinglePoleLaurentExtraction g x (r/2)`.
  -- `U := ball x r` (open, contains `closedBall x (r/2)`).
  -- `h_x z := (z-x)^(n+N) • F(z-x)`. Note `n + N ≥ 0` always, so this is a
  -- genuine analytic function near `x` (no inverse powers).
  -- Principal coefficients: `a k := c (N-k)` if `1 ≤ k ≤ N` else `0`. We use
  -- the algebra `c_{N-k} * (z-x)^(-k) = c_{N-k} * (z-x)^(N-k) * (z-x)^(-N)`.
  refine ⟨N, fun k => c (N - k),
          fun z => (z - x) ^ ((n + N : ℤ)) • F (z - x), ball x r,
          isOpen_ball, ?_, ?_, ?_⟩
  · -- `closedBall x (r/2) ⊆ ball x r`.
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  · -- `DifferentiableOn ℂ h_x (ball x r)`.
    -- `h_x z = (z-x)^(n+N) • F(z-x)`. We have `n + N ≥ 0`, so the power is
    -- a genuine analytic function. Combined with `F ∘ (·-x)` analytic on
    -- `ball x r ⊆ ball x δ`, the product is analytic, hence differentiable.
    have hnN_nonneg : 0 ≤ n + N := by
      by_cases hn_sign : 0 ≤ n
      · have hN0 : N = 0 := by
          simp [hN_def, Int.toNat_of_nonpos (by linarith : -n ≤ 0)]
        simp [hN0]
        exact hn_sign
      · push_neg at hn_sign
        have hN_eq : (N : ℤ) = -n := by
          simp [hN_def, Int.toNat_of_nonneg (by linarith : 0 ≤ -n)]
        linarith
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ((M : ℤ) = n + N) :=
      ⟨(n + N).toNat, by simp [Int.toNat_of_nonneg hnN_nonneg]⟩
    have hF_anOn_r : AnalyticOnNhd ℂ F (Metric.ball 0 r) :=
      hF_anOn.mono (Metric.ball_subset_ball (min_le_left _ _))
    have h_sub : ∀ z ∈ Metric.ball x r, z - x ∈ Metric.ball (0 : ℂ) r := by
      intro z hz
      rw [Metric.mem_ball] at hz ⊢
      simpa [dist_eq_norm] using hz
    -- The function `z ↦ (z-x)^(n+N) • F(z-x) = (z-x)^M • F(z-x)`.
    have h_an : AnalyticOnNhd ℂ
        (fun z : ℂ => (z - x) ^ ((n + N : ℤ)) • F (z - x))
        (Metric.ball x r) := by
      intro z hz
      have h_sub_an : AnalyticAt ℂ (fun z : ℂ => z - x) z :=
        (analyticAt_id (𝕜 := ℂ) (x := z)).sub analyticAt_const
      have hF_at : AnalyticAt ℂ (fun z : ℂ => F (z - x)) z :=
        (hF_anOn_r (z - x) (h_sub z hz)).comp h_sub_an
      -- `(z-x) ^ M = (z-x) ^ ((n+N : ℤ))` via `zpow_natCast`.
      have h_pow_at : AnalyticAt ℂ (fun z : ℂ => (z - x) ^ M) z :=
        h_sub_an.pow M
      have h_zpow_eq : (fun z : ℂ => (z - x) ^ ((n + N : ℤ)))
          = (fun z : ℂ => (z - x) ^ M) := by
        funext w
        rw [← hM, zpow_natCast]
      have h_zpow_at : AnalyticAt ℂ (fun z : ℂ => (z - x) ^ ((n + N : ℤ))) z := by
        rw [h_zpow_eq]; exact h_pow_at
      exact h_zpow_at.smul hF_at
    exact h_an.differentiableOn
  · -- The Laurent decomposition on `ball x r \ {x}`.
    intro z hz_mem hz_ne
    rw [Metric.mem_ball] at hz_mem
    have hzx_ne : z - x ≠ 0 := sub_ne_zero.mpr hz_ne
    have h_dist_lt_r₀ : dist z x < r₀ := lt_of_lt_of_le hz_mem (min_le_right _ _)
    -- Meromorphic factorisation at `z`.
    have h_meq : g z = (z - x) ^ n • G z := hG_eq_ball h_dist_lt_r₀ hz_ne
    -- Taylor expansion of `G ∘ (·+x)` at `w := z - x`.
    have hF_at_z : G z = (∑ i ∈ Finset.range N, (z - x) ^ i • c i)
        + (z - x) ^ N • F (z - x) := by
      have := hF_eq' (z - x)
      simpa [sub_add_cancel] using this
    -- Now compute. Both sides are scalar multiplications in ℂ; rewrite as products.
    -- We show: g z = (z-x)^(n+N) • F(z-x) + ∑_{k=1}^{N} c (N-k) * (z-x)^(-k).
    -- Strategy: Multiply Taylor identity by `(z-x)^n`, and re-index the sum.
    rw [h_meq, hF_at_z, smul_add]
    -- The remainder term: `(z-x)^n • ((z-x)^N • F(z-x)) = (z-x)^(n+N) • F(z-x)`.
    have h_rem :
        ((z - x) ^ n) • ((z - x) ^ N • F (z - x))
          = ((z - x) ^ ((n + N : ℤ))) • F (z - x) := by
      simp only [smul_eq_mul, ← mul_assoc]
      congr 1
      rw [zpow_add₀ hzx_ne]
      simp [zpow_natCast]
    rw [h_rem]
    -- The principal sum term: convert
    -- `(z-x)^n • ∑_{i<N} (z-x)^i • c_i` to `∑_{k=1..N} c_{N-k} * (z-x)^(-k)`.
    -- Case split on whether `N = 0` or `N > 0`. When `N = 0`, the principal-part
    -- sum is empty on both sides and the identity is trivial. When `N > 0`, the
    -- order is `≤ 0`, and from `N = (-n).toNat > 0` we deduce `n ≤ 0` and
    -- `(N : ℤ) = -n`, i.e. `n + N = 0`. This is the algebraic identity we need.
    by_cases hN0 : N = 0
    · -- `N = 0`: the principal sum is empty.
      subst hN0
      simp
    · -- `N > 0`: the order is genuinely negative, `n = -(N : ℤ)`.
      have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
      have hn_neg : n < 0 := by
        by_contra h_not_neg
        push_neg at h_not_neg
        have : N = 0 := by simp [hN_def, Int.toNat_of_nonpos (by linarith : -n ≤ 0)]
        exact hN0 this
      have hN_eq : (N : ℤ) = -n := by
        simp [hN_def, Int.toNat_of_nonneg (by linarith : 0 ≤ -n)]
      have h_sum :
          ((z - x) ^ n) • (∑ i ∈ Finset.range N, (z - x) ^ i • c i)
            = ∑ k ∈ Finset.Icc 1 N, c (N - k) * (z - x) ^ (-(k : ℤ)) := by
        simp only [smul_eq_mul, Finset.mul_sum]
        -- Re-index: bijection `k ↦ N - k` from `Icc 1 N` onto `range N`.
        rw [show (Finset.range N : Finset ℕ) = (Finset.Icc 1 N).image (fun k => N - k) from ?_]
        · rw [Finset.sum_image (by
              intro a ha b hb hab
              rw [Finset.mem_Icc] at ha hb
              omega)]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Finset.mem_Icc] at hk
          obtain ⟨hk1, hk2⟩ := hk
          -- After the bijection, the summand at `k` is the original summand at `i = N-k`:
          -- `(z-x)^n * ((z-x)^(N-k) * c (N-k))`. We must show this equals
          -- `c (N-k) * (z-x)^(-k:ℤ)`.
          have h_pow_eq : (z - x) ^ n * (z - x) ^ (N - k) = (z - x) ^ (-(k : ℤ)) := by
            -- Convert `^ : ℂ → ℕ` to `^ : ℂ → ℤ` and apply `zpow_add₀`.
            have h_natCast : ((N - k : ℕ) : ℤ) = -n - k := by
              have : ((N - k : ℕ) : ℤ) = (N : ℤ) - k := by
                push_cast; omega
              rw [this, hN_eq]
            rw [show ((z - x) ^ (N - k) : ℂ) = (z - x) ^ ((N - k : ℕ) : ℤ) from
                  (zpow_natCast (z - x) (N - k)).symm,
                ← zpow_add₀ hzx_ne, h_natCast]
            congr 1
            ring
          calc (z - x) ^ n * ((z - x) ^ (N - k) * c (N - k))
              = c (N - k) * ((z - x) ^ n * (z - x) ^ (N - k)) := by ring
            _ = c (N - k) * (z - x) ^ (-(k : ℤ)) := by rw [h_pow_eq]
        · ext i
          simp only [Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
          constructor
          · intro hi; refine ⟨N - i, ⟨by omega, by omega⟩, by omega⟩
          · rintro ⟨k, ⟨_, hk2⟩, rfl⟩; omega
      rw [h_sum]

end MultiPoleLaurentExistence

end JacobianChallenge

end
