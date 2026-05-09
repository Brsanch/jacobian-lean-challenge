/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.AnalyticKthRoot

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local meromorphy of the norm pushforward (Phase 1.1 chip P1.1b, ZZ201)

This file is the analytic follow-on to `NormPushforwardLocal.lean` (P1.1a, ZZ200,
algebraic μ_k-symmetry).  The headline result here is local meromorphy of
the planar norm pushforward `normPow g k` at any **regular** value
`t₀ : ℂ` with `t₀ ≠ 0`, given that `g : ℂ → ℂ` is `MeromorphicAt` at every
preimage `ζ * s₀` (with `ζ ∈ μ_k` and `s₀` any chosen `k`-th root of `t₀`).

## Strategy at a regular value `t₀ ≠ 0`

The map `t ↦ t` itself is analytic and non-vanishing in a neighbourhood of
`t₀`, so by `analytic_kth_root_of_nonvanishing` (already in the repo) there
exists an analytic function `r : ℂ → ℂ` defined on a closed disc
around `t₀` with `r(t)^k = t` everywhere on the disc.  In particular
`r(t)` is a smoothly varying choice of `k`-th root of `t`.

The set `nthRootsFinset k t` then admits the bijective parameterization
`ζ ↦ ζ * r(t)` from `nthRootsFinset k 1`, so
  `normPow g k t = ∏ ζ ∈ nthRootsFinset k 1, g (ζ * r(t))`
on a disc around `t₀` minus the origin (the equality is shipped by
`normPow_pow` from P1.1a applied to `s = r(t)`).

This expresses `normPow g k` *locally near `t₀`* as a finite product of
meromorphic functions of `t` (each factor `t ↦ g (ζ * r(t))` is a
composition of a meromorphic `g` at `ζ * r(t₀)` with the analytic map
`t ↦ ζ * r(t)`), so `MeromorphicAt (normPow g k) t₀` follows from
`MeromorphicAt.fun_prod` and `MeromorphicAt.comp_analyticAt`.

## What this file ships

* `nthRootsFinset_eq_image_of_analytic_root`
  — for an analytic root `r` with `r(t)^k = t` and `t ≠ 0`,
  `nthRootsFinset k t = (nthRootsFinset k 1).image (· * r(t))`.
* `normPow_eq_prod_mu_k_of_root`
  — pointwise reduction `normPow g k t = ∏ ζ ∈ μ_k, g (ζ * r(t))` for `t ≠ 0`.
* `normPow_meromorphicAt_of_regular`
  — `MeromorphicAt (normPow g k) t₀` whenever `t₀ ≠ 0`, `1 ≤ k`,
  and `g` is `MeromorphicAt` at each `ζ * s₀` for `ζ ∈ μ_k`,
  where `s₀` is any chosen `k`-th root of `t₀`.

## Residual / not in this file

* The branch case `t₀ = 0` is **deferred**.  The intended descent —
  meromorphy of the auxiliary `H s := ∏ ζ ∈ μ_k, g (ζ * s)` at `s = 0`
  is immediate from `MeromorphicAt.fun_prod`; descending to meromorphy
  of `normPow g k` at `t = s^k` requires either a symmetric-function /
  Newton-identity descent (analytic functions invariant under μ_k action
  in the variable `s` are analytic functions of `s^k`) or a direct
  Riemann-removable-singularity argument on `normPow g k`.  Neither is
  available off-the-shelf in mathlib at the pinned revision
  `8e3c989...`, so we ship the regular case unconditionally and leave
  the branch case to a downstream chip.

* The manifold-level finite-fibre wrapper
  `NormFM : (X → Y) → MeromorphicNonzero X → Y → ℂ` and its local
  meromorphy at a manifold point `y₀ : Y` are similarly downstream:
  on a chart neighbourhood of a regular value of `f`, the manifold-level
  fibre product reduces to a finite product of pulled-back meromorphic
  germs (no branching), which is meromorphic by the same lemma stack;
  on a chart of a branch value, the chart pullback `F z = w₀ + (ψ z)^k`
  reduces precisely to the planar `normPow` problem.  We isolate the
  planar regular case here so it can be reused on either side.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* All identifiers ASCII (no `ω` binders, per Lean 4.30 reservation).
-/

noncomputable section

open Polynomial Finset Complex Metric

namespace JacobianChallenge
namespace Manifold

universe u

/-! ### From an analytic `k`-th root branch to the orbit parameterization
of `nthRootsFinset k t`. -/

/-- If `r(t)` is any `k`-th root of `t : ℂ` and `t ≠ 0` (so `r(t) ≠ 0`),
then the set of all `k`-th roots of `t` is the μ_k-orbit of `r(t)`. -/
lemma nthRootsFinset_eq_image_of_root
    {k : ℕ} (hk : 1 ≤ k) {t : ℂ} (ht : t ≠ 0) {rt : ℂ} (hrt : rt ^ k = t) :
    Polynomial.nthRootsFinset k t
      = (Polynomial.nthRootsFinset k (1 : ℂ)).image (fun ζ => ζ * rt) := by
  classical
  have hrt_ne : rt ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hrt
    exact ht hrt.symm
  ext x
  constructor
  · intro hx
    rw [Polynomial.mem_nthRootsFinset hk] at hx
    -- x ^ k = t = rt ^ k, so (x / rt) ^ k = 1.
    refine Finset.mem_image.mpr ⟨x * rt⁻¹, ?_, ?_⟩
    · rw [Polynomial.mem_nthRootsFinset hk]
      have : (x * rt⁻¹) ^ k = x ^ k * (rt ^ k)⁻¹ := by
        rw [mul_pow, inv_pow]
      rw [this, hx, hrt, mul_inv_cancel₀ ht]
    · rw [mul_assoc, inv_mul_cancel₀ hrt_ne, mul_one]
  · intro hx
    obtain ⟨ζ, hζ, hxζ⟩ := Finset.mem_image.mp hx
    rw [Polynomial.mem_nthRootsFinset hk] at hζ
    rw [Polynomial.mem_nthRootsFinset hk, ← hxζ, mul_pow, hζ, one_mul, hrt]

/-- The map `ζ ↦ ζ * rt` is injective on `nthRootsFinset k 1` whenever
`rt ≠ 0`.  (We use this for `Finset.prod_image`-style rewrites.) -/
lemma mulRight_injOn_of_ne_zero
    {rt : ℂ} (hrt : rt ≠ 0) (S : Finset ℂ) :
    Set.InjOn (fun ζ : ℂ => ζ * rt) S := by
  intro ζ₁ _ ζ₂ _ h
  exact mul_right_cancel₀ hrt h

/-! ### Pointwise reduction of `normPow` along an analytic root. -/

/-- Pointwise reduction: if `r(t)` is a `k`-th root of `t` with `t ≠ 0`
and `1 ≤ k`, then
`normPow g k t = ∏ ζ ∈ nthRootsFinset k 1, g (ζ * r(t))`. -/
lemma normPow_eq_prod_mu_k_of_root
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {t : ℂ} (ht : t ≠ 0)
    {rt : ℂ} (hrt : rt ^ k = t) :
    normPow g k t
      = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * rt) := by
  classical
  have hrt_ne : rt ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hrt
    exact ht hrt.symm
  -- `t = rt^k` and `rt ≠ 0`, so by `normPow_pow` applied at `s := rt`.
  have h1 : normPow g k (rt ^ k)
      = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * rt) :=
    normPow_pow g hk hrt_ne
  rw [← hrt]; exact h1

/-! ### Meromorphy of `normPow g k` at a regular value `t₀ ≠ 0`.

The argument:

1. Choose any `k`-th root `s₀` of `t₀`; we'll show `MeromorphicAt (normPow g k) t₀`.
2. By `analytic_kth_root_of_nonvanishing` applied to `u := id` at `t₀`,
   we get an analytic function `r : ℂ → ℂ` on a closed disc around `t₀`
   with `r(t)^k = t` on the disc.
3. By `normPow_eq_prod_mu_k_of_root`, on the punctured disc
   `normPow g k t = ∏ ζ ∈ μ_k, g (ζ * r(t))`.
4. Each summand `t ↦ g (ζ * r(t))` is a composition of `g` (meromorphic at
   `ζ * r(t₀)`) with `t ↦ ζ * r(t)` (analytic at `t₀`), hence meromorphic
   at `t₀` by `MeromorphicAt.comp_analyticAt`.
5. The finite product of meromorphic germs is meromorphic by
   `MeromorphicAt.fun_prod`.
6. Two meromorphic germs that agree off a non-isolated set agree as
   meromorphic germs (`MeromorphicAt.congr` with eventual equality on
   the punctured neighbourhood).
-/

/-- Identity is analytic everywhere (used as the input to the analytic
`k`-th root supplier). -/
private lemma analyticOnNhd_id_closedBall (t₀ : ℂ) (ρ : ℝ) :
    AnalyticOnNhd ℂ (fun t : ℂ => t) (Metric.closedBall t₀ ρ) := by
  intro t _
  exact analyticAt_id

/-- **Local meromorphy of the norm pushforward at a regular value.**

Let `g : ℂ → ℂ`, `1 ≤ k`, `t₀ ≠ 0`, and `s₀` any `k`-th root of `t₀`.
If `g` is `MeromorphicAt` at every point of the form `ζ * s₀` for
`ζ ∈ nthRootsFinset k 1`, then `normPow g k` is `MeromorphicAt` at `t₀`.

This is the regular branch of the multiplicative pushforward across the
planar `k`-th-power map: away from the branch value `t = 0`, the `k`
preimages are k disjoint analytic branches of the `k`-th root, and the
fibre product is a finite product of meromorphic germs of `g` pulled
back along those branches. -/
theorem normPow_meromorphicAt_of_regular
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    {s₀ : ℂ} (hs₀ : s₀ ^ k = t₀)
    (hg : ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
      MeromorphicAt g (ζ * s₀)) :
    MeromorphicAt (normPow g k) t₀ := by
  classical
  -- Step 1: extract an analytic k-th root branch r near t₀.
  have hρ : (0 : ℝ) < 1 := by norm_num
  have hu_id : AnalyticOnNhd ℂ (fun t : ℂ => t) (Metric.closedBall t₀ 1) :=
    analyticOnNhd_id_closedBall t₀ 1
  have ht₀_in : (fun t : ℂ => t) t₀ ≠ 0 := ht₀
  obtain ⟨r, ρ', hρ'_pos, _hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing (u := fun t : ℂ => t) (x₀ := t₀)
      (ρ := 1) (k := k) hρ hu_id ht₀_in hk
  -- Step 2: r is analytic at t₀ in particular.
  have hr_at : AnalyticAt ℂ r t₀ := hr_an t₀ (Metric.mem_closedBall_self hρ'_pos.le)
  -- r(t₀) is a k-th root of t₀.
  have hr_t0_pow : (r t₀) ^ k = t₀ :=
    hr_pow t₀ (Metric.mem_closedBall_self hρ'_pos.le)
  -- r(t₀) ≠ 0.
  have hr_t0_ne : r t₀ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hr_t0_pow
    exact ht₀ hr_t0_pow.symm
  -- The two k-th roots r(t₀) and s₀ of t₀ are related: r(t₀) = ζ_r * s₀ for some ζ_r ∈ μ_k.
  have h_pow_eq : (r t₀) ^ k = s₀ ^ k := by rw [hr_t0_pow, hs₀]
  set ζr : ℂ := r t₀ * s₀⁻¹ with hζr_def
  have hs₀_ne : s₀ ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hs₀
    exact ht₀ hs₀.symm
  have hζr_pow : ζr ^ k = 1 := by
    rw [hζr_def, mul_pow, inv_pow, hr_t0_pow, hs₀, mul_inv_cancel₀ ht₀]
  have hζr_mem : ζr ∈ Polynomial.nthRootsFinset k (1 : ℂ) :=
    (Polynomial.mem_nthRootsFinset hk (1 : ℂ)).mpr hζr_pow
  have hr_t0_eq : r t₀ = ζr * s₀ := by
    rw [hζr_def, mul_assoc, inv_mul_cancel₀ hs₀_ne, mul_one]
  -- Step 3: define the candidate finite product F, show it is meromorphic at t₀.
  set F : ℂ → ℂ := fun t =>
    ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * r t) with hF_def
  have hF_mero : MeromorphicAt F t₀ := by
    refine MeromorphicAt.fun_prod (s := Polynomial.nthRootsFinset k (1 : ℂ))
      (F := fun ζ t => g (ζ * r t)) ?_
    intro ζ hζ
    -- Show: MeromorphicAt (fun t => g (ζ * r t)) t₀.
    -- Inner map: t ↦ ζ * r t, analytic at t₀.
    have h_inner : AnalyticAt ℂ (fun t : ℂ => ζ * r t) t₀ :=
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ζ) t₀).mul hr_at
    -- Value of inner at t₀: ζ * r(t₀) = ζ * (ζr * s₀) = (ζ * ζr) * s₀.
    have h_val : (fun t : ℂ => ζ * r t) t₀ = (ζ * ζr) * s₀ := by
      show ζ * r t₀ = (ζ * ζr) * s₀
      rw [hr_t0_eq]; ring
    -- ζ * ζr ∈ μ_k, since both are.
    have hζζr_mem : ζ * ζr ∈ Polynomial.nthRootsFinset k (1 : ℂ) := by
      rw [Polynomial.mem_nthRootsFinset hk] at hζ
      rw [Polynomial.mem_nthRootsFinset hk]
      rw [mul_pow, hζ, hζr_pow, mul_one]
    -- g is MeromorphicAt (ζ * ζr) * s₀ by hypothesis.
    have hg_at : MeromorphicAt g (ζ * ζr * s₀) := hg (ζ * ζr) hζζr_mem
    -- Compose.
    have h_comp : MeromorphicAt (g ∘ (fun t : ℂ => ζ * r t)) t₀ := by
      have := MeromorphicAt.comp_analyticAt
        (f := g) (g := fun t : ℂ => ζ * r t) (x := t₀)
        (by rw [h_val]; exact hg_at) h_inner
      exact this
    -- Convert g ∘ _ to a fun-form.
    exact h_comp
  -- Step 4: F equals normPow g k on a punctured neighbourhood of t₀.
  have ht₀_mem_int : t₀ ∈ Metric.ball t₀ ρ' := Metric.mem_ball_self hρ'_pos
  -- On the open ball minus 0 (plus t₀ itself? actually we need eventual equality
  -- on a punctured neighbourhood of t₀; t₀ ≠ 0, so the open ball around t₀ is
  -- eventually contained in `{t | t ≠ 0}`).
  have h_ball_open : IsOpen (Metric.ball t₀ ρ') := Metric.isOpen_ball
  have h_ne_zero_eventually : ∀ᶠ t in nhds t₀, t ≠ 0 :=
    (continuous_id.continuousAt (x := t₀)).eventually_ne ht₀
  have h_ball_eventually : ∀ᶠ t in nhds t₀, t ∈ Metric.ball t₀ ρ' :=
    h_ball_open.mem_nhds ht₀_mem_int
  -- For t ∈ ball t₀ ρ' ⊂ closedBall t₀ ρ', r t is a k-th root of t (from hr_pow).
  have h_eq : (normPow g k) =ᶠ[nhds t₀] F := by
    filter_upwards [h_ball_eventually, h_ne_zero_eventually] with t ht_ball ht_ne
    have ht_cb : t ∈ Metric.closedBall t₀ ρ' := Metric.ball_subset_closedBall ht_ball
    have hrt_pow : r t ^ k = t := hr_pow t ht_cb
    -- Apply normPow_eq_prod_mu_k_of_root.
    exact normPow_eq_prod_mu_k_of_root g hk ht_ne hrt_pow
  -- Step 5: meromorphy is preserved by eventual equality.
  -- We need eventual equality on `nhdsWithin t₀ {t₀}ᶜ`. `nhds t₀` refines that.
  refine hF_mero.congr ?_
  exact (h_eq.symm).filter_mono nhdsWithin_le_nhds

/-- A convenience repackaging: at a regular value `t₀ ≠ 0`, if `g` is
meromorphic on the entire μ_k-orbit `{ζ * s₀ : ζ^k = 1}` of any chosen
`k`-th root `s₀` of `t₀`, then `normPow g k` is meromorphic at `t₀`.
This is just a renaming of `normPow_meromorphicAt_of_regular`. -/
theorem normPow_meromorphicAt_regular_of_meromorphic_on_orbit
    (g : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k) {t₀ : ℂ} (ht₀ : t₀ ≠ 0)
    {s₀ : ℂ} (hs₀ : s₀ ^ k = t₀)
    (hg : ∀ x ∈ (Polynomial.nthRootsFinset k (1 : ℂ)).image (fun ζ => ζ * s₀),
      MeromorphicAt g x) :
    MeromorphicAt (normPow g k) t₀ := by
  refine normPow_meromorphicAt_of_regular g hk ht₀ hs₀ ?_
  intro ζ hζ
  apply hg
  exact Finset.mem_image.mpr ⟨ζ, hζ, rfl⟩

end Manifold
end JacobianChallenge

end
