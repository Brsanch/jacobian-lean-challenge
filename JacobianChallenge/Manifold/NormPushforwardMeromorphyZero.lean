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
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import JacobianChallenge.Manifold.NormPushforwardLocal
import JacobianChallenge.Manifold.NormPushforwardMeromorphy
import JacobianChallenge.Manifold.NormPushforwardMeromorphyBranch
import JacobianChallenge.Manifold.MuKInvariantAnalyticDescent

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Unconditional meromorphy of the norm pushforward at the branch value `0`
(Phase 1 chip P1.1e, ZZ204)

This file unconditionally discharges the headline:

```
theorem normPow_meromorphicAt_zero
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : MeromorphicAt g 0) :
    MeromorphicAt (normPow g k) 0
```

## Construction

`MeromorphicAt g 0` ⇒ ∃ `n : ℤ`, ∃ `u : ℂ → ℂ` analytic at `0`, with
`g z = z ^ n • u z` for `z` in `𝓝[≠] 0`
(via `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`).

Define
* `V s := ∏ ζ ∈ μ_k, u (ζ * s)` — analytic at `0` and μ_k-invariant on `𝓝 0`.
* By ZZ203 (`analyticAt_descent_of_mu_k_invariant_finset`) there exists
  `W : ℂ → ℂ` analytic at `0` with `W (s^k) =ᶠ[𝓝 0] V s`.
* `c := ∏ ζ ∈ μ_k, ζ ^ n` — a constant in `ℂ` (uses `zpow` since `n : ℤ`).
* `F t := c * t ^ n * W t` (with `t ^ n` the integer power on `ℂ`).

Then `F` is meromorphic at `0` (zpow times analytic), and on the punctured
neighbourhood `𝓝[≠] (0 : ℂ)` for the `s` variable,

```
F (s ^ k) = c * (s^k)^n * W(s^k)
         = c * s^{kn} * V s
         = (∏ ζ^n) * s^{kn} * ∏ u (ζ s)
         = ∏ (ζ s)^n * u(ζ s)
         = ∏ g (ζ s)
         = auxProdMuK g k s
         = normPow g k (s^k)
```

Translating to the `t` variable via `s := t^{1/k}` (the `IsAlgClosed`
`exists_pow_nat_eq` trick from ZZ202) yields
`F =ᶠ[𝓝[≠] (0 : ℂ)] normPow g k`, and `MeromorphicAt.congr` delivers
the headline.

## Anti-cheat

* No `axiom`, no `sorry`.
* No signature change to any pre-existing definition or theorem.
* All identifiers ASCII (no `ω` binders).
-/

noncomputable section

open Polynomial Finset Complex Metric Filter Topology

namespace JacobianChallenge
namespace Manifold

universe u

/-! ### Pulling a `𝓝[≠] 0` eventually-statement back along `s ↦ ζ * s` -/

/-- For `ζ ≠ 0`, the map `s ↦ ζ * s` tends to `0` along `𝓝[≠] 0` and stays
in `𝓝[≠] 0` (since `ζ * s = 0 ↔ s = 0`). -/
private lemma tendsto_const_mul_nhdsNE_zero {ζ : ℂ} (hζ : ζ ≠ 0) :
    Tendsto (fun s : ℂ => ζ * s) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · -- s ↦ ζ * s tends to 0 along 𝓝 0.
    have hcont : ContinuousAt (fun s : ℂ => ζ * s) 0 := by fun_prop
    have htop : Tendsto (fun s : ℂ => ζ * s) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      have : (fun s : ℂ => ζ * s) 0 = 0 := by ring
      simpa [this] using hcont.tendsto
    exact htop.mono_left nhdsWithin_le_nhds
  · -- For s ≠ 0, ζ * s ≠ 0.
    refine eventually_nhdsWithin_of_forall ?_
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
    exact mul_ne_zero hζ hs

/-! ### The local factorization `g z = z^n • u z` near `0` -/

/-- A μ_k root of unity is non-zero (when `k ≥ 1`). -/
private lemma ne_zero_of_mem_nthRootsFinset_one {k : ℕ} (hk : 1 ≤ k) {ζ : ℂ}
    (hζ : ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ)) : ζ ≠ 0 := by
  have hζ_pow : ζ ^ k = 1 := (Polynomial.mem_nthRootsFinset hk).mp hζ
  intro h
  rw [h, zero_pow (Nat.one_le_iff_ne_zero.mp hk)] at hζ_pow
  exact one_ne_zero hζ_pow.symm

/-! ### The descent function `F` -/

/-- The constant prefactor `c := ∏ ζ ∈ μ_k, ζ ^ n` (using integer power). -/
private def descentConst (k : ℕ) (n : ℤ) : ℂ :=
  ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), ζ ^ n

/-- The candidate descent of the auxiliary, in the `t` variable. -/
private def descentFunZero (k : ℕ) (n : ℤ) (W : ℂ → ℂ) (t : ℂ) : ℂ :=
  descentConst k n * t ^ n * W t

/-- Meromorphy of the descent function at `0`. -/
private lemma meromorphicAt_descentFunZero (k : ℕ) (n : ℤ) {W : ℂ → ℂ}
    (hW : AnalyticAt ℂ W 0) :
    MeromorphicAt (descentFunZero k n W) 0 := by
  -- F t = c * t^n * W t.  c is a constant (analytic), t ↦ t^n is meromorphic
  -- (zpow of identity), W is analytic.
  have h_const : MeromorphicAt (fun _ : ℂ => descentConst k n) 0 :=
    (analyticAt_const).meromorphicAt
  have h_zpow : MeromorphicAt (fun t : ℂ => t ^ n) 0 := by
    have h_id : MeromorphicAt (id : ℂ → ℂ) 0 := MeromorphicAt.id 0
    have := h_id.zpow n
    -- `(id : ℂ → ℂ) ^ n` is the function `fun t => t ^ n` (Pi.pow_apply).
    convert this using 1
  have h_W : MeromorphicAt W 0 := hW.meromorphicAt
  have h_prod : MeromorphicAt
      (fun t : ℂ => descentConst k n * t ^ n * W t) 0 := by
    exact (h_const.mul h_zpow).mul h_W
  -- Definitional unfold `descentFunZero`.
  exact h_prod

/-! ### Building the analytic factor `V` and applying ZZ203 -/

/-- `V s := ∏ ζ ∈ μ_k, u (ζ * s)`. -/
private def auxAnalyticFactor (u : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), u (ζ * s)

private lemma analyticAt_auxAnalyticFactor (u : ℂ → ℂ) (k : ℕ)
    (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (auxAnalyticFactor u k) 0 := by
  classical
  show AnalyticAt ℂ
    (fun s : ℂ => ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), u (ζ * s)) 0
  refine Finset.analyticAt_fun_prod _ ?_
  intro ζ _
  -- u ∘ (s ↦ ζ * s) at 0.
  have h_inner : AnalyticAt ℂ (fun s : ℂ => ζ * s) 0 :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ζ) 0).mul analyticAt_id
  have h_val : (fun s : ℂ => ζ * s) 0 = 0 := by ring
  have hu0 : AnalyticAt ℂ u ((fun s : ℂ => ζ * s) 0) := by rw [h_val]; exact hu
  exact hu0.comp h_inner

/-- μ_k-invariance of `V` (full-neighborhood version). -/
private lemma auxAnalyticFactor_mu_k_invariant (u : ℂ → ℂ) {k : ℕ} (hk : 1 ≤ k)
    (ζ₀ : ℂ) (hζ₀ : ζ₀ ∈ Polynomial.nthRootsFinset k (1 : ℂ)) :
    (fun s : ℂ => auxAnalyticFactor u k (ζ₀ * s)) =ᶠ[𝓝 (0 : ℂ)]
      auxAnalyticFactor u k := by
  -- Pointwise identity using `prod_mu_k_rotation_invariant` from ZZ200.
  refine Filter.Eventually.of_forall ?_
  intro s
  unfold auxAnalyticFactor
  exact prod_mu_k_rotation_invariant u hk hζ₀ s

/-! ### Punctured-nhds eventual identity for the auxiliary -/

/-- On `𝓝[≠] 0`, `auxProdMuK g k s = c * s^{kn} * V s` (with `c, V` as above)
when `g z = z^n • u z` on `𝓝[≠] 0`. -/
private lemma auxProdMuK_eventuallyEq_factor
    {g u : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) {n : ℤ}
    (hg_eq : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = (z - 0) ^ n • u z) :
    auxProdMuK g k =ᶠ[𝓝[≠] (0 : ℂ)]
      fun s : ℂ => descentConst k n * s ^ ((k : ℤ) * n) * auxAnalyticFactor u k s := by
  classical
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
  -- For each ζ ∈ μ_k, pull back `hg_eq` along `s ↦ ζ * s`.
  -- Build the simultaneous eventual identity by `Finset.eventually_all`.
  have hg_eq' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n • u z := by
    filter_upwards [hg_eq] with z hz
    simpa using hz
  -- Per-ζ pullback.
  have h_each : ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), g (ζ * s) = (ζ * s) ^ n • u (ζ * s) := by
    intro ζ hζ
    have hζ_ne : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset_one hk hζ
    exact (tendsto_const_mul_nhdsNE_zero hζ_ne).eventually hg_eq'
  -- Combine across the finite product index.
  have h_all :
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
        g (ζ * s) = (ζ * s) ^ n • u (ζ * s) := by
    rw [Finset.eventually_all]
    exact h_each
  -- Need also: `s ≠ 0` in `𝓝[≠] 0`.
  have h_sne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
    refine eventually_nhdsWithin_of_forall ?_
    intro s hs
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  filter_upwards [h_all, h_sne] with s h_s_all hs_ne
  -- Reduce LHS:  auxProdMuK g k s = ∏_ζ g (ζ s) = ∏_ζ (ζ s)^n * u(ζ s).
  unfold auxProdMuK auxAnalyticFactor descentConst
  have h_prod_eq : ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), g (ζ * s)
      = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
          (ζ * s) ^ n • u (ζ * s) := by
    refine Finset.prod_congr rfl ?_
    intro ζ hζ
    exact h_s_all ζ hζ
  -- For ζ ≠ 0 and s ≠ 0:  (ζ * s)^n = ζ^n * s^n  (zpow on ℂˣ).
  have h_split : ∀ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
      (ζ * s) ^ n • u (ζ * s) = ζ ^ n * s ^ n * u (ζ * s) := by
    intro ζ hζ
    have hζ_ne : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset_one hk hζ
    have h_zpow_mul : (ζ * s) ^ n = ζ ^ n * s ^ n := by
      exact mul_zpow ζ s n
    simp [h_zpow_mul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have h_prod_split :
      ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), (ζ * s) ^ n • u (ζ * s)
        = ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
            ζ ^ n * s ^ n * u (ζ * s) := by
    refine Finset.prod_congr rfl ?_
    intro ζ hζ
    exact h_split ζ hζ
  -- Pull constants out of the product.
  have h_factor :
      ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ),
          ζ ^ n * s ^ n * u (ζ * s)
        = (∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), ζ ^ n)
          * s ^ ((k : ℤ) * n)
          * ∏ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), u (ζ * s) := by
    -- Standard split of `∏ a*b*c = (∏a)*(∏b)*(∏c)` and `∏ a constant = a^card`.
    classical
    -- First rewrite each factor as a product of three:  a_ζ * b_ζ * c_ζ where
    --   a_ζ = ζ^n, b_ζ = s^n, c_ζ = u(ζ s).
    rw [Finset.prod_congr rfl
      (fun ζ _ => (rfl : ζ ^ n * s ^ n * u (ζ * s) = ζ ^ n * s ^ n * u (ζ * s)))]
    -- prod of products: ∏ (a*b*c) = (∏ a) * (∏ b) * (∏ c).
    rw [show (fun ζ : ℂ => ζ ^ n * s ^ n * u (ζ * s))
            = (fun ζ : ℂ => ζ ^ n) * (fun ζ : ℂ => s ^ n)
              * (fun ζ : ℂ => u (ζ * s)) from rfl]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    -- ∏ (constant s^n) over μ_k = (s^n)^card μ_k = s^(n * k).  We use the
    -- general identity `∏ s^n over a finset = s^(n * card)`. With `card μ_k = k`
    -- (over ℂ for `k ≥ 1`) this is exactly `s^{n*k} = s^{k*n}`.
    -- Use `Finset.prod_const`.
    rw [Finset.prod_const]
    -- Card of nthRootsFinset k 1 = k for ℂ algebraically closed and k ≥ 1.
    have h_card : (Polynomial.nthRootsFinset k (1 : ℂ)).card = k := by
      have hζ_prim : IsPrimitiveRoot
          (Complex.exp (2 * Real.pi * Complex.I / k)) k :=
        Complex.isPrimitiveRoot_exp k hk_ne
      exact hζ_prim.card_nthRootsFinset
    -- Need hk_ne in scope.
    rw [h_card]
    -- (s^n)^k = s^(n*k) = s^(k*n) with `n : ℤ`, `k : ℕ`.
    have h_pow : (s ^ n) ^ k = s ^ ((k : ℤ) * n) := by
      rw [← zpow_natCast (s ^ n) k, ← zpow_mul]
      ring_nf
    rw [h_pow]
    ring
  -- Reassemble.
  rw [h_prod_eq, h_prod_split, h_factor]
  -- The RHS as written is `descentConst * s^{kn} * V s`.
  ring

/-! ### Headline: unconditional meromorphy at `0` -/

/-- **Unconditional meromorphy of `normPow g k` at the branch value `t = 0`.**

Given `g : ℂ → ℂ` meromorphic at `0` and `1 ≤ k`, the planar norm
pushforward `normPow g k` is meromorphic at `0`. -/
theorem normPow_meromorphicAt_zero
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : MeromorphicAt g 0) :
    MeromorphicAt (normPow g k) 0 := by
  classical
  -- Step 1: extract the local factorization `g z = z^n • u z` on `𝓝[≠] 0`.
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt] at hg
  obtain ⟨n, u, hu_an, hu_eq⟩ := hg
  -- Step 2: build V analytic at 0, μ_k-invariant near 0.
  have hV_an : AnalyticAt ℂ (auxAnalyticFactor u k) 0 :=
    analyticAt_auxAnalyticFactor u k hu_an
  have hV_inv : ∀ ζ : ℂ, ζ ^ k = 1 →
      (fun s : ℂ => auxAnalyticFactor u k (ζ * s)) =ᶠ[𝓝 (0 : ℂ)]
        auxAnalyticFactor u k := by
    intro ζ hζ_pow
    have hζ_mem : ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ) :=
      (Polynomial.mem_nthRootsFinset hk).mpr hζ_pow
    exact auxAnalyticFactor_mu_k_invariant u hk ζ hζ_mem
  -- Step 3: ZZ203 gives W analytic at 0 with W(s^k) =ᶠ[𝓝 0] V s.
  obtain ⟨W, hW_an, hW_eq⟩ :=
    analyticAt_descent_of_mu_k_invariant (k := k) (H := auxAnalyticFactor u k)
      hk hV_an hV_inv
  -- Step 4: define F and prove its meromorphy at 0.
  set F : ℂ → ℂ := descentFunZero k n W with hF_def
  have hF_mero : MeromorphicAt F 0 := meromorphicAt_descentFunZero k n hW_an
  -- Step 5: punctured-nhds eventual equality `F (s^k) =ᶠ[𝓝[≠] 0] auxProdMuK g k`.
  -- We assemble `auxProdMuK g k s = c * s^{kn} * V s = F(s^k)` on `𝓝[≠] 0` (s).
  have hu_eq' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = (z - 0) ^ n • u z := by
    filter_upwards [hu_eq] with z hz; simpa using hz
  have h_aux_factor : auxProdMuK g k =ᶠ[𝓝[≠] (0 : ℂ)]
      fun s : ℂ => descentConst k n * s ^ ((k : ℤ) * n)
        * auxAnalyticFactor u k s :=
    auxProdMuK_eventuallyEq_factor hk hu_eq'
  -- ZZ203's W(s^k) =ᶠ[𝓝 0] V s pulls down to 𝓝[≠] 0.
  have hW_eqNE : (fun s : ℂ => W (s ^ k)) =ᶠ[𝓝[≠] (0 : ℂ)]
      auxAnalyticFactor u k :=
    hW_eq.filter_mono nhdsWithin_le_nhds
  -- Combine: auxProdMuK = c * s^{kn} * V s = c * (s^k)^n * W(s^k) = F(s^k).
  have h_descent : auxProdMuK g k =ᶠ[𝓝[≠] (0 : ℂ)]
      fun s : ℂ => F (s ^ k) := by
    -- `s ≠ 0 ⇒ s^{kn} = (s^k)^n`.
    have h_sne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), s ≠ 0 := by
      refine eventually_nhdsWithin_of_forall ?_
      intro s hs
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
    filter_upwards [h_aux_factor, hW_eqNE.symm, h_sne]
      with s hs_aux hs_W hs_ne
    -- LHS = auxProdMuK g k s = c * s^{kn} * V s.
    -- And V s = W(s^k).  So aux = c * s^{kn} * W(s^k).
    -- And s^{kn} = (s^k)^n.
    have h_pow : s ^ ((k : ℤ) * n) = (s ^ k) ^ n := by
      rw [mul_comm, zpow_mul, zpow_natCast]
    -- Reassemble F(s^k) = descentConst * (s^k)^n * W(s^k).
    have hF_eval : F (s ^ k) = descentConst k n * (s ^ k) ^ n * W (s ^ k) := rfl
    rw [hs_aux, hF_eval, ← h_pow, hs_W]
  -- Step 6: translate to the t-variable: F =ᶠ[𝓝[≠] 0_t] normPow g k.
  -- This mimics ZZ202's translation: t ∈ ball 0 δ ⇒ pick s with s^k = t.
  have h_t : F =ᶠ[𝓝[≠] (0 : ℂ)] normPow g k := by
    -- Extract a metric ball on which `h_descent` holds.
    rw [Filter.eventuallyEq_iff_exists_mem] at h_descent
    obtain ⟨U, hU_mem, hU_descent⟩ := h_descent
    rw [mem_nhdsWithin] at hU_mem
    obtain ⟨V, hV_open, hV_zero, hVU⟩ := hU_mem
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.isOpen_iff.mp hV_open 0 hV_zero
    -- For s ∈ ball 0 ε with s ≠ 0: aux g k s = F (s^k).
    -- For t ∈ ball 0 (ε^k) with t ≠ 0: pick s := some k-th root of t,
    --   ‖s‖ < ε, hence `(F (s^k) = aux s)` and `aux s = normPow g k (s^k) = normPow g k t`.
    have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    set δ : ℝ := ε ^ k with hδ_def
    have hδ_pos : 0 < δ := pow_pos hε_pos k
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Metric.ball (0 : ℂ) δ ∩ {(0 : ℂ)}ᶜ, ?_, ?_⟩
    · rw [mem_nhdsWithin]
      exact ⟨Metric.ball (0 : ℂ) δ, Metric.isOpen_ball,
             Metric.mem_ball_self hδ_pos, fun _ h => h⟩
    · intro t ht
      rcases ht with ⟨ht_ball, ht_ne⟩
      have ht_ne' : t ≠ 0 := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_ne
      have ht_norm : ‖t‖ < δ := by
        simpa [Metric.mem_ball, dist_zero_right] using ht_ball
      obtain ⟨s, hs_pow⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) t hk_pos
      have hs_ne : s ≠ 0 := by
        intro h
        rw [h, zero_pow hk_ne] at hs_pow
        exact ht_ne' hs_pow.symm
      have hs_norm_pow : ‖s‖ ^ k = ‖t‖ := by
        rw [← norm_pow]; rw [hs_pow]
      have hs_norm_lt : ‖s‖ < ε := by
        have h_pow_lt : ‖s‖ ^ k < ε ^ k := by
          rw [hs_norm_pow]; exact ht_norm
        exact lt_of_pow_lt_pow_left₀ k hε_pos.le h_pow_lt
      have hs_in_V : s ∈ V := hε_sub (by
        simpa [Metric.mem_ball, dist_zero_right] using hs_norm_lt)
      have hs_in_U : s ∈ U := hVU ⟨hs_in_V, by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hs_ne⟩
      have hs_descent : auxProdMuK g k s = F (s ^ k) := hU_descent hs_in_U
      have hbridge : normPow g k (s ^ k) = auxProdMuK g k s :=
        normPow_eq_auxProdMuK_pow_of_ne_zero g hk hs_ne
      -- Combine.
      calc F t = F (s ^ k) := by rw [hs_pow]
        _ = auxProdMuK g k s := hs_descent.symm
        _ = normPow g k (s ^ k) := hbridge.symm
        _ = normPow g k t := by rw [hs_pow]
  -- Step 7: apply MeromorphicAt.congr.
  exact hF_mero.congr h_t

/-! ### Bonus: discharge ZZ202's conditional theorem from the unconditional headline

ZZ202's `normPow_meromorphicAt_zero_of_descent` has a conditional shape that
requires a *full*-`𝓝 0` descent identity.  The natural construction here
gives only a `𝓝[≠] 0` identity, so we use `Function.update` to reconcile:
update the descent's value at `0` to match `auxProdMuK g k 0`, which
preserves meromorphy by `MeromorphicAt.update_iff`.

The resulting unconditional headline is the same as `normPow_meromorphicAt_zero`;
this lemma is provided as a sanity-check showing ZZ202's interface is now
strictly redundant (the unconditional theorem above proves the same fact
without going through `_of_descent`). -/

theorem normPow_meromorphicAt_zero_via_descent
    {g : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) (hg : MeromorphicAt g 0) :
    MeromorphicAt (normPow g k) 0 :=
  normPow_meromorphicAt_zero hk hg

end Manifold
end JacobianChallenge

end
