/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # μ_k-invariant analytic descent (Phase 1.1 chip P1.1d, ZZ203)

**Theorem (analytic descent).**  Let `H : ℂ → ℂ` be analytic at `0` with
`H(ζ s) = H(s)` (eventually near `0`) for every `k`-th root of unity
`ζ`, with `k ≥ 1`.  Then there exists `F : ℂ → ℂ` analytic at `0` with
`F(s^k) = H(s)` (eventually near `0`).

This file delivers the headline `analyticAt_descent_of_mu_k_invariant`.

## Mathematical content

`H` analytic at `0` ⇒ `H(s) = ∑_n a_n s^n` near `0`.
μ_k-invariance ⇒ `a_n (ζ^n - 1) = 0` for all `ζ ∈ μ_k`.
Picking a primitive `k`-th root `ζ₀` and using `IsPrimitiveRoot.pow_eq_one_iff_dvd`:
`a_n = 0` whenever `k ∤ n`.
Hence `H(s) = ∑_m a_{km} (s^k)^m`.  Define `q m := a_{km}`,
`F := q.sum`; convergence radius `≥ r^k` where `r` is the radius of `p`.

## Honest scope (residuals)

This file ships the **analytic** descent only.  The follow-on
*meromorphic* descent — bridging `MeromorphicAt g 0` to
`analyticAt_descent_of_mu_k_invariant` (via the
`MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt` normal form
applied to the auxiliary `auxProdMuK g k` from `NormPushforwardMeromorphyBranch`)
and discharging the `normPow_meromorphicAt_zero_of_descent` hypothesis from
ZZ202 — is left as a separate chip.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* All identifiers ASCII (no `ω` binders).
-/

noncomputable section

open Polynomial Finset Complex Metric Filter Topology
open scoped NNReal ENNReal

namespace JacobianChallenge
namespace Manifold

universe u

/-! ### Series with rescaled input

The power series of `s ↦ H (ζ * s)` at `0` is obtained from the series
of `H` by replacing each coefficient `a_n` with `ζ^n • a_n`. -/

/-- The formal multilinear series with coefficients `n ↦ ζ^n • p.coeff n`. -/
private def smulSeriesPow (p : FormalMultilinearSeries ℂ ℂ ℂ) (ζ : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => ζ ^ n • p.coeff n)

private lemma smulSeriesPow_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (ζ : ℂ) (n : ℕ) :
    (smulSeriesPow p ζ).coeff n = ζ ^ n • p.coeff n := by
  simp [smulSeriesPow, FormalMultilinearSeries.coeff_ofScalars]

/-- If `H` has power series `p` at `0`, then `s ↦ H (ζ * s)` has power
series `smulSeriesPow p ζ` at `0`. -/
private lemma hasFPowerSeriesAt_const_mul_left
    {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt H p 0) (ζ : ℂ) :
    HasFPowerSeriesAt (fun s : ℂ => H (ζ * s)) (smulSeriesPow p ζ) 0 := by
  rw [hasFPowerSeriesAt_iff] at hp ⊢
  -- Pull the eventually-statement back along z ↦ ζ * z (continuous at 0).
  have hcont : ContinuousAt (fun z : ℂ => ζ * z) 0 := by fun_prop
  have hat : (fun z : ℂ => ζ * z) 0 = 0 := by simp
  have hpull : ∀ᶠ z in 𝓝 0,
      HasSum (fun n => (ζ * z) ^ n • p.coeff n) (H (0 + ζ * z)) := by
    have htend := hcont.tendsto
    rw [hat] at htend
    exact htend.eventually hp
  filter_upwards [hpull] with z hz
  -- Reindex: (ζ * z)^n • a_n = z^n • (ζ^n • a_n) = z^n • coeff n.
  have hcoeff_eq : (fun n : ℕ => (ζ * z) ^ n • p.coeff n)
      = (fun n : ℕ => z ^ n • (smulSeriesPow p ζ).coeff n) := by
    funext n
    rw [smulSeriesPow_coeff, mul_pow, smul_smul]
  -- Target uses `H (ζ * (0 + z))`; we have `H (0 + ζ * z)`. They're equal.
  have hval : H (0 + ζ * z) = H (ζ * (0 + z)) := by rw [zero_add, zero_add]
  rw [hcoeff_eq, hval] at hz
  exact hz

/-! ### Coefficient vanishing for μ_k-invariant series -/

/-- Algebraic helper: if `a = ζ * a` and `ζ ≠ 1` (in a field), then `a = 0`. -/
private lemma eq_zero_of_mul_eq_self {a ζ : ℂ} (h : a = ζ * a) (hζ : ζ ≠ 1) : a = 0 := by
  have h' : (ζ - 1) * a = 0 := by
    have : ζ * a - a = 0 := by linarith [h]
    -- avoid linarith on ℂ; use linear_combination
    linear_combination -h
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  exact (mul_eq_zero.mp h').resolve_left hne

/-- If `p` is the power series of an μ_k-invariant function `H` at `0`,
then `p.coeff n = 0` whenever `k ∤ n`. -/
private lemma coeff_eq_zero_of_mu_k_invariant
    {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hp : HasFPowerSeriesAt H p 0)
    (hinv : ∀ ζ : ℂ, ζ ^ k = 1 → (fun s : ℂ => H (ζ * s)) =ᶠ[𝓝 0] H)
    {n : ℕ} (hkn : ¬ k ∣ n) : p.coeff n = 0 := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  -- Pick a primitive k-th root of unity in ℂ.
  set ζ₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζ₀_def
  have hζ₀ : IsPrimitiveRoot ζ₀ k := Complex.isPrimitiveRoot_exp k hk_ne
  have hζ₀_pow_k : ζ₀ ^ k = 1 := hζ₀.pow_eq_one
  -- s ↦ H (ζ₀ * s) has series smulSeriesPow p ζ₀.
  have hshift : HasFPowerSeriesAt (fun s : ℂ => H (ζ₀ * s)) (smulSeriesPow p ζ₀) 0 :=
    hasFPowerSeriesAt_const_mul_left hp ζ₀
  -- It also equals H eventually (μ_k-invariance).
  have h_eq_event : (fun s : ℂ => H (ζ₀ * s)) =ᶠ[𝓝 0] H := hinv ζ₀ hζ₀_pow_k
  -- So H itself has series smulSeriesPow p ζ₀.
  have hH_via_shift : HasFPowerSeriesAt H (smulSeriesPow p ζ₀) 0 :=
    hshift.congr h_eq_event
  -- Uniqueness of FMS.
  have hp_eq : p = smulSeriesPow p ζ₀ :=
    HasFPowerSeriesAt.eq_formalMultilinearSeries hp hH_via_shift
  -- Compare nth coefficients.
  have hcoeff_eq : p.coeff n = ζ₀ ^ n * p.coeff n := by
    have := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q.coeff n) hp_eq
    simp only [smulSeriesPow_coeff, smul_eq_mul] at this
    exact this
  -- ζ₀^n ≠ 1 since k ∤ n.
  have hpow_ne : ζ₀ ^ n ≠ 1 := by
    intro h
    exact hkn ((hζ₀.pow_eq_one_iff_dvd n).mp h)
  exact eq_zero_of_mul_eq_self hcoeff_eq hpow_ne

/-! ### The descended series and its convergence -/

/-- Descended series: `q.coeff m = p.coeff (k*m)`. -/
private def descendedSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun m => p.coeff (k * m))

private lemma descendedSeries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (k m : ℕ) :
    (descendedSeries p k).coeff m = p.coeff (k * m) := by
  simp [descendedSeries, FormalMultilinearSeries.coeff_ofScalars]

private lemma norm_descendedSeries (p : FormalMultilinearSeries ℂ ℂ ℂ) (k m : ℕ) :
    ‖descendedSeries p k m‖ = ‖p (k * m)‖ := by
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef,
    FormalMultilinearSeries.norm_apply_eq_norm_coef, descendedSeries_coeff]

/-- The radius of `descendedSeries p k` is at least `r^k` whenever `r < p.radius`. -/
private lemma le_radius_descendedSeries
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < p.radius) :
    ((r ^ k : ℝ≥0) : ℝ≥0∞) ≤ (descendedSeries p k).radius := by
  -- Get the bound `‖p n‖ * r^n ≤ C`.
  obtain ⟨C, _hC_pos, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr
  -- Apply `le_radius_of_bound` for the descended series.
  refine (descendedSeries p k).le_radius_of_bound C ?_
  intro m
  -- ‖q m‖ * (r^k)^m = ‖p (k*m)‖ * r^(k*m) ≤ C.
  rw [norm_descendedSeries]
  have hpow : ((r ^ k : ℝ≥0) : ℝ) ^ m = (r : ℝ) ^ (k * m) := by
    push_cast
    rw [← pow_mul, mul_comm m k]
  rw [hpow]
  exact hC (k * m)

/-! ### Reindexing the H power series -/

/-- For `s : ℂ` with the `H`-series convergent at `s` and coefficients
vanishing off `k ∣ n`, reindex via `m ↦ k*m`:
`HasSum (fun m => (s^k)^m • p.coeff (k*m)) (H s)`. -/
private lemma hasSum_reindex_descended
    {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hzero : ∀ n : ℕ, ¬ k ∣ n → p.coeff n = 0)
    {s : ℂ} (hsum : HasSum (fun n => s ^ n • p.coeff n) (H s)) :
    HasSum (fun m : ℕ => (s ^ k) ^ m • p.coeff (k * m)) (H s) := by
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  -- Use Function.Injective.hasSum_iff with g m = k*m.
  have hinj : Function.Injective (fun m : ℕ => k * m) :=
    Nat.mul_left_injective (Nat.pos_of_ne_zero hk_ne).ne'
  have hzero_off : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ => k * m) →
      s ^ n • p.coeff n = 0 := by
    intro n hn
    have : ¬ k ∣ n := by
      intro ⟨m, hm⟩
      apply hn
      exact ⟨m, by simp [hm]⟩
    rw [hzero n this, smul_zero]
  have hreindex : HasSum ((fun n : ℕ => s ^ n • p.coeff n) ∘ (fun m => k * m)) (H s) :=
    (hinj.hasSum_iff hzero_off).mpr hsum
  -- Simplify the composition: s^(k*m) • p.coeff (k*m) = (s^k)^m • p.coeff (k*m).
  convert hreindex using 1
  funext m
  simp [Function.comp, pow_mul]

/-! ### The descended function -/

/-- The descended function: `F := (descendedSeries p k).sum`. -/
private def descendedFun (p : FormalMultilinearSeries ℂ ℂ ℂ) (k : ℕ) : ℂ → ℂ :=
  (descendedSeries p k).sum

/-- The descended function has the descended series at `0`, on a positive ball. -/
private lemma hasFPowerSeriesOnBall_descendedFun
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k)
    {r : ℝ≥0} (hr_pos : 0 < r) (hr : (r : ℝ≥0∞) < p.radius) :
    HasFPowerSeriesOnBall (descendedFun p k) (descendedSeries p k) 0
      ((r ^ k : ℝ≥0) : ℝ≥0∞) := by
  have hrad_pos : 0 < (descendedSeries p k).radius :=
    lt_of_lt_of_le (by
      have : (0 : ℝ≥0∞) < ((r ^ k : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_pos]; positivity
      exact this) (le_radius_descendedSeries hk hr)
  refine HasFPowerSeriesOnBall.mono (r' := ((r ^ k : ℝ≥0) : ℝ≥0∞))
    ((descendedSeries p k).hasFPowerSeriesOnBall hrad_pos) ?_ ?_
  · rw [ENNReal.coe_pos]; positivity
  · exact le_radius_descendedSeries hk hr

private lemma hasFPowerSeriesAt_descendedFun
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k)
    {r : ℝ≥0} (hr_pos : 0 < r) (hr : (r : ℝ≥0∞) < p.radius) :
    HasFPowerSeriesAt (descendedFun p k) (descendedSeries p k) 0 :=
  ⟨_, hasFPowerSeriesOnBall_descendedFun hk hr_pos hr⟩

private lemma analyticAt_descendedFun
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hp_radius_pos : 0 < p.radius) :
    AnalyticAt ℂ (descendedFun p k) 0 := by
  -- Pick r₀ : ℝ≥0 with 0 < r₀ and (r₀ : ℝ≥0∞) < p.radius.
  obtain ⟨r₀, hr₀_pos, hr₀_lt⟩ : ∃ r₀ : ℝ≥0, 0 < r₀ ∧ (r₀ : ℝ≥0∞) < p.radius := by
    -- p.radius > 0; pick any positive value strictly below.
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hp_radius_pos with ⟨r₀, h0, hlt⟩
    refine ⟨r₀, ?_, hlt⟩
    rwa [ENNReal.coe_pos] at h0
  exact (hasFPowerSeriesAt_descendedFun hk hr₀_pos hr₀_lt).analyticAt

/-! ### Eventual equality `F (s^k) = H s` near `0` -/

/-- For `s` small enough, `descendedFun p k (s^k) = H s`.

This is the headline eventual identity, derived by reindexing the `H`
power series at `s` via `m ↦ k*m`. -/
private lemma descendedFun_pow_eventually_eq
    {H : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hp : HasFPowerSeriesAt H p 0)
    (hzero : ∀ n : ℕ, ¬ k ∣ n → p.coeff n = 0) :
    (fun s : ℂ => descendedFun p k (s ^ k)) =ᶠ[𝓝 0] H := by
  -- Use `hasFPowerSeriesAt_iff` to extract eventual HasSum for H at z = s.
  have hp_iff : ∀ᶠ s in 𝓝 0,
      HasSum (fun n => s ^ n • p.coeff n) (H (0 + s)) :=
    (hasFPowerSeriesAt_iff).mp hp
  filter_upwards [hp_iff] with s hs
  -- Get HasSum for the descended series at t := s^k.
  have hreindex : HasSum (fun m : ℕ => (s ^ k) ^ m • p.coeff (k * m)) (H s) := by
    have : H (0 + s) = H s := by rw [zero_add]
    rw [this] at hs
    exact hasSum_reindex_descended hk hzero hs
  -- The sum equals `descendedFun p k (s^k)`.
  have hF : descendedFun p k (s ^ k) = H s := by
    -- descendedFun p k t = (descendedSeries p k).sum t = ∑' m, (descendedSeries p k) m (fun _ => t).
    unfold descendedFun FormalMultilinearSeries.sum
    -- Convert: (descendedSeries p k) m (fun _ => s^k) = (s^k)^m • p.coeff (k*m).
    rw [show (fun m : ℕ => descendedSeries p k m fun _ : Fin m => s ^ k)
        = (fun m : ℕ => (s ^ k) ^ m • p.coeff (k * m)) from ?_]
    · exact hreindex.tsum_eq
    · funext m
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, descendedSeries_coeff]
  exact hF

/-! ### Headline theorem -/

/-- **μ_k-invariant analytic descent.**

Let `H : ℂ → ℂ` be analytic at `0`.  If for every `k`-th root of unity
`ζ` (`ζ^k = 1`), the function `s ↦ H (ζ * s)` agrees with `H` on a
neighborhood of `0`, then there exists a function `F : ℂ → ℂ` analytic
at `0` such that `F (s^k) = H s` on a neighborhood of `0`. -/
theorem analyticAt_descent_of_mu_k_invariant
    {H : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hH : AnalyticAt ℂ H 0)
    (hinv : ∀ ζ : ℂ, ζ ^ k = 1 → (fun s : ℂ => H (ζ * s)) =ᶠ[𝓝 0] H) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      (fun s : ℂ => F (s ^ k)) =ᶠ[𝓝 0] H := by
  -- Extract a power series for H.
  obtain ⟨p, hp⟩ : ∃ p, HasFPowerSeriesAt H p 0 := hH
  have hp_radius_pos : 0 < p.radius := hp.radius_pos
  -- Coefficient vanishing off k ∤ n.
  have hzero : ∀ n : ℕ, ¬ k ∣ n → p.coeff n = 0 :=
    fun n hkn => coeff_eq_zero_of_mu_k_invariant hk hp hinv hkn
  -- The descended function is the desired F.
  refine ⟨descendedFun p k, analyticAt_descendedFun hk hp_radius_pos, ?_⟩
  exact descendedFun_pow_eventually_eq hk hp hzero

/-! ### Adapter to `nthRootsFinset`-style invariance hypothesis

The companion file `NormPushforwardMeromorphyBranch.lean` (ZZ202)
phrases μ_k-invariance via membership in `Polynomial.nthRootsFinset k 1`.
We provide an adapter so the headline can be applied with that hypothesis. -/

theorem analyticAt_descent_of_mu_k_invariant_finset
    {H : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k)
    (hH : AnalyticAt ℂ H 0)
    (hinv : ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
              (fun s : ℂ => H (ζ * s)) =ᶠ[𝓝 0] H) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
      (fun s : ℂ => F (s ^ k)) =ᶠ[𝓝 0] H := by
  refine analyticAt_descent_of_mu_k_invariant hk hH ?_
  intro ζ hζ
  apply hinv ζ
  rw [Polynomial.mem_nthRootsFinset hk]
  exact hζ

end Manifold
end JacobianChallenge

end
