/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalKFoldMultiplicityFullyUnconditional
import JacobianChallenge.Manifold.LocalMultiplicityInvariance
import JacobianChallenge.Manifold.AnalyticLocalFactorization
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Bridge: critical set ↔ chart-pullback derivative zero (ZZ99)

This file supplies the **bridge lemma** that ZZ97's *topological* definition

```
criticalSet f := { x | ¬ ∃ U ∈ 𝓝 x, Set.InjOn (f̃) U }
```

coincides with the *analytic* "chart-pullback derivative vanishes" condition
consumed downstream.

## Pieces

* **`deriv_ne_zero_of_analyticOrderAt_eq_one`** — order-`1` ⇒ deriv ≠ `0`.
  From the factorization `g(z) - w₀ = (z - x₀) · u(z)` with `u(x₀) ≠ 0`
  (ZZ90), the product rule gives `deriv g x₀ = u(x₀) ≠ 0`.

* **`analyticOrderAt_ge_two_of_deriv_zero`** — deriv = `0` ⇒ order ≥ `2`,
  under `g x₀ = w₀` and "not eventually constant near `x₀`". The
  "not eventually constant" hypothesis is required to rule out
  `analyticOrderAt = ⊤` (the locally-constant case).

* **`notInjOn_iff_deriv_zero_of_analytic`** — the headline planar lemma:
  for analytic `g : ℂ → ℂ` at `x₀` not eventually equal to `g x₀` near
  `x₀`,

  `(¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U) ↔ deriv g x₀ = 0`.

  *Forward.* If not InjOn, then `deriv g x₀ ≠ 0` would (by the inverse
  function theorem packaged via `HasStrictFDerivAt.toOpenPartialHomeomorph`)
  produce an open neighbourhood of `x₀` on which `g` is injective — a
  contradiction. So `deriv g x₀ = 0`.

  *Reverse.* If `deriv g x₀ = 0`, then by `analyticOrderAt_ge_two_of_deriv_zero`
  the local order `k = analyticOrderAt (g - g x₀) x₀` is `≥ 2`. ZZ92 then
  gives, for some `ε, δ > 0`, that every `w ∈ ball (g x₀) δ \ {g x₀}` has
  exactly `k ≥ 2` preimages in `ball x₀ ε`. Two distinct preimages in any
  neighbourhood of `x₀` (after shrinking via the local
  `KthRootSubstitution` bundle) violate `InjOn g U`.

* **`criticalSet_iff_chart_pullback_deriv_zero`** — manifold-side
  translation. Given a chart-package recording the chart pullback,
  its analyticity, and its non-degeneracy, we transport the planar
  statement to the manifold side.

No `sorry`, no `axiom`. No signature changes outside this new file.
-/

@[expose] public section

noncomputable section

open scoped Topology
open Set Filter Metric

namespace JacobianChallenge
namespace Manifold

/-! ## Step 1. `analyticOrderAt = 1` ⇒ `deriv ≠ 0` -/

/-- **From `analyticOrderAt (g - w₀) x₀ = 1` to `deriv g x₀ ≠ 0`.**

If `g` is analytic at `x₀` with `g x₀ = w₀` and the analytic order of
`g - w₀` at `x₀` is exactly `1`, then `deriv g x₀ ≠ 0`.

Proof: ZZ90 (`analytic_local_factorization`) gives `R > 0` and a
non-vanishing analytic factor `u` on `closedBall x₀ R` with
`g z - w₀ = (z - x₀) ^ 1 * u z`. So `g(z) = w₀ + (z - x₀) * u(z)`. The
product rule gives `deriv g x₀ = u(x₀) ≠ 0`. -/
theorem deriv_ne_zero_of_analyticOrderAt_eq_one
    {g : ℂ → ℂ} {x₀ w₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (1 : ℕ∞)) :
    deriv g x₀ ≠ 0 := by
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization (k := 1) (le_refl _) hg h_w₀ hord
  have hball_subset : Metric.ball x₀ R ⊆ Metric.closedBall x₀ R :=
    Metric.ball_subset_closedBall
  have hg_eq : ∀ z ∈ Metric.ball x₀ R, g z = w₀ + (z - x₀) * u z := by
    intro z hz
    have h1 := hfact z (hball_subset hz)
    have h2 : (z - x₀) ^ (1 : ℕ) * u z = (z - x₀) * u z := by rw [pow_one]
    have h3 : g z - w₀ = (z - x₀) * u z := h1.trans h2
    have h4 : g z = w₀ + (z - x₀) * u z := by
      have := sub_eq_iff_eq_add'.mp h3
      linear_combination this
    exact h4
  set h : ℂ → ℂ := fun z => w₀ + (z - x₀) * u z with hh_def
  have hu_at_x₀ : AnalyticAt ℂ u x₀ :=
    hu_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  have hu_diff : DifferentiableAt ℂ u x₀ := hu_at_x₀.differentiableAt
  have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
    differentiableAt_id.sub (differentiableAt_const x₀)
  have hball_nhds : Metric.ball x₀ R ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ hR_pos
  have hg_h_eventually : g =ᶠ[𝓝 x₀] h := by
    filter_upwards [hball_nhds] with z hz using hg_eq z hz
  have hderiv_sub : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
    have hd := deriv_sub (𝕜 := ℂ) (differentiableAt_id) (differentiableAt_const x₀)
    simp at hd
    exact hd
  have hderiv_prod :
      deriv (fun z : ℂ => (z - x₀) * u z) x₀ = u x₀ := by
    have hp := deriv_mul (𝕜 := ℂ) hsub_diff hu_diff
    rw [hderiv_sub, sub_self, zero_mul, add_zero, one_mul] at hp
    exact hp
  have hsplit : deriv (fun z : ℂ => w₀ + (z - x₀) * u z) x₀
      = deriv (fun z : ℂ => (z - x₀) * u z) x₀ := by
    have hd_const : DifferentiableAt ℂ (fun _ : ℂ => w₀) x₀ :=
      differentiableAt_const w₀
    have hd_prod : DifferentiableAt ℂ (fun z : ℂ => (z - x₀) * u z) x₀ :=
      hsub_diff.mul hu_diff
    have h_add := deriv_add (𝕜 := ℂ) hd_const hd_prod
    simp at h_add
    exact h_add
  have hderiv_h : deriv h x₀ = u x₀ := by
    show deriv (fun z : ℂ => w₀ + (z - x₀) * u z) x₀ = u x₀
    rw [hsplit, hderiv_prod]
  have hderiv_g : deriv g x₀ = deriv h x₀ := hg_h_eventually.deriv_eq
  rw [hderiv_g, hderiv_h]
  exact hu_x₀

/-! ## Step 2. Order ≥ 2 from deriv = 0 -/

/-- If `g` is analytic at `x₀`, `g x₀ = w₀`, and `g` is not eventually
equal to `w₀` near `x₀`, then `analyticOrderAt (g - w₀) x₀` equals some
finite natural number `k ≥ 1`. -/
private lemma analyticOrderAt_eq_natCast_ge_one_of_not_eventually
    {g : ℂ → ℂ} {x₀ w₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hne : ¬ ∀ᶠ z in 𝓝 x₀, g z = w₀) :
    ∃ k : ℕ, 1 ≤ k ∧ analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞) := by
  set f : ℂ → ℂ := fun z => g z - w₀ with hf_def
  have hf_an : AnalyticAt ℂ f x₀ :=
    hg.sub (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => w₀) x₀)
  have hf_x₀ : f x₀ = 0 := by simp [hf_def, h_w₀]
  have hf_ne : ¬ ∀ᶠ z in 𝓝 x₀, f z = 0 := by
    intro hcontra
    apply hne
    filter_upwards [hcontra] with z hz
    have : g z - w₀ = 0 := hz
    exact sub_eq_zero.mp this
  -- Case analysis on `analyticOrderAt f x₀` ∈ ℕ∞ = WithTop ℕ.
  rcases h_ord : analyticOrderAt f x₀ with _ | k
  · -- order = ⊤. Then `f` is eventually 0, contradicting `hf_ne`.
    exfalso
    apply hf_ne
    -- Use mathlib: `analyticOrderAt = ⊤ ↔ eventually 0` for analytic functions.
    -- We use `hf_an.eventually_eq_zero_or_eventually_ne_zero` and rule out the
    -- non-zero case via the `WithTop` lemma `AnalyticAt.analyticOrderAt_eq_natCast`.
    rcases hf_an.eventually_eq_zero_or_eventually_ne_zero with hz | hne'
    · exact hz
    · -- `hne' : ∀ᶠ z in 𝓝[≠] x₀, f z ≠ 0` — but `analyticOrderAt = ⊤` says `f` is
      -- eventually 0. Show contradiction by extracting a sequence of zeros forced
      -- by `eventually_eq_zero_or_eventually_ne_zero` not happening.
      -- Actually: if order = ⊤, `f =ᶠ 0` near `x₀`. We use `WithTop` directly:
      -- order = ⊤ ⟹ the Taylor series is identically zero ⟹ f is locally zero.
      -- We cite `AnalyticAt.frequently_zero_iff_eventually_zero` (mathlib has both
      -- directions). Concretely: `hne'` says f is *not* eventually zero (only
      -- eventually nonzero on the punctured side — but combined with `f x₀ = 0`,
      -- which is not eventually nonzero, this gives "f frequently zero" which by
      -- the analytic identity theorem implies eventually zero.
      -- We avoid calling `hne'` directly and just prove `f =ᶠ 0` via order = ⊤
      -- using `analyticOrderAt`'s `WithTop.add_top` style lemma. Easiest route:
      -- contradiction with `hne'` directly.
      -- `f x₀ = 0`, but `hne'` is on the punctured nbhd, so doesn't include `x₀`.
      -- We use `AnalyticAt.eventually_eq_zero_iff_analyticOrderAt_eq_top`-style.
      -- Bare-hands approach: order = ⊤ and `hne'` together. By `hne'`, there's a
      -- punctured nbhd where `f ≠ 0`. By order = ⊤, the formal Taylor series at
      -- x₀ is zero, so `f` is locally zero (mathlib's `AnalyticAt.locally_zero_iff`).
      -- We invoke `hf_an.analyticOrderAt_eq_natCast` at `k = 0`: it would say
      -- `f x₀ ≠ 0`, but we have `f x₀ = 0`. That's not directly useful since
      -- `analyticOrderAt = ⊤ ≠ (0 : ℕ∞)`, so `analyticOrderAt_eq_natCast` doesn't apply.
      --
      -- Direct route: use `AnalyticAt.eventually_eq_zero_of_analyticOrderAt_eq_top`
      -- if it exists at this pin. We try the dot-notation form.
      have : ∀ᶠ z in 𝓝 x₀, f z = 0 := by
        -- Convert the WithTop value via mathlib API. The standard name is
        -- `AnalyticAt.locally_zero_iff_analyticOrderAt_eq_top` — let's just use
        -- an alternative: build a contradiction from `hne'` and a frequently-zero
        -- argument coming from order = ⊤.
        --
        -- Strategy: use `hf_an.eventually_eq_zero_or_eventually_ne_zero` already
        -- returned `hne'`. So if order = ⊤, there's a tension. Mathlib should
        -- bridge this. We rely on `AnalyticAt.analyticOrderAt_eq_top`:
        exact hf_an.analyticOrderAt_eq_top.mp h_ord
      exact this
  · -- order = k ∈ ℕ. Show k ≥ 1 (else f x₀ ≠ 0 contradicts hf_x₀ = 0).
    refine ⟨k, ?_, rfl⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
    · exfalso
      subst hk0
      -- order = 0 ⟹ ∃ u with `f =ᶠ u` near x₀ and `u x₀ ≠ 0`. So `f x₀ = u x₀ ≠ 0`.
      have h_eq_nat : analyticOrderAt f x₀ = ((0 : ℕ) : ℕ∞) := h_ord
      obtain ⟨u, _hu_an, hu_x₀, hu_eq⟩ := hf_an.analyticOrderAt_eq_natCast.mp h_eq_nat
      -- `hu_eq : f =ᶠ[𝓝 x₀] (z - x₀)^0 * u z = u z`. Evaluate at `x₀`.
      rw [Filter.EventuallyEq] at hu_eq
      have : f x₀ = (x₀ - x₀) ^ (0 : ℕ) * u x₀ := hu_eq.self_of_nhds
      rw [pow_zero, one_mul] at this
      have : f x₀ ≠ 0 := this ▸ hu_x₀
      exact this hf_x₀
    · exact hk_pos

/-- **Order ≥ 2 from vanishing derivative.**

For analytic `g : ℂ → ℂ` at `x₀` with `g x₀ = w₀`, not eventually
equal to `w₀` near `x₀`, and `deriv g x₀ = 0`, the analytic order of
`g - w₀` at `x₀` is at least `2`. -/
theorem analyticOrderAt_ge_two_of_deriv_zero
    {g : ℂ → ℂ} {x₀ w₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hne : ¬ ∀ᶠ z in 𝓝 x₀, g z = w₀)
    (hd : deriv g x₀ = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (fun z => g z - w₀) x₀ := by
  obtain ⟨k, hk_ge_one, hk_eq⟩ :=
    analyticOrderAt_eq_natCast_ge_one_of_not_eventually hg h_w₀ hne
  rw [hk_eq]
  by_contra hlt
  push_neg at hlt
  have hk_lt_two : k < 2 := by exact_mod_cast hlt
  interval_cases k
  exact (deriv_ne_zero_of_analyticOrderAt_eq_one hg h_w₀ hk_eq) hd

/-! ## Step 3. The headline planar lemma -/

/-- **Forward direction (factored out).** If `g` is analytic at `x₀`
with `deriv g x₀ ≠ 0`, then there is an open neighbourhood of `x₀` on
which `g` is injective. -/
private lemma injOn_nhds_of_deriv_ne_zero
    {g : ℂ → ℂ} {x₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀) (hd : deriv g x₀ ≠ 0) :
    ∃ U ∈ 𝓝 x₀, Set.InjOn g U := by
  have hsd : HasStrictDerivAt g (deriv g x₀) x₀ := hg.hasStrictDerivAt
  have hsfd :
      HasStrictFDerivAt g
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv g x₀) hd) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd.hasStrictFDerivAt_equiv hd
  let φ : OpenPartialHomeomorph ℂ ℂ := hsfd.toOpenPartialHomeomorph g
  have hx0_src : x₀ ∈ φ.source := hsfd.mem_toOpenPartialHomeomorph_source
  have h_src_nhds : φ.source ∈ 𝓝 x₀ := φ.open_source.mem_nhds hx0_src
  have h_inj : Set.InjOn (φ : ℂ → ℂ) φ.source := φ.injOn
  have h_coe : (φ : ℂ → ℂ) = g := hsfd.toOpenPartialHomeomorph_coe
  refine ⟨φ.source, h_src_nhds, ?_⟩
  rw [← h_coe]; exact h_inj

/-- **Reverse direction (factored out).** Order `≥ 2` implies, in any
neighbourhood `U ∈ 𝓝 x₀`, the existence of two distinct points with the
same `g`-value — hence `g` is not injective on `U`.

Proof: extract the `KthRootSubstitution` bundle (analytic factor `v`
with `v(x₀) = 0`, `deriv v x₀ ≠ 0`, `g - w₀ = v^k`). Apply ZZ74 to `v`:
on a small ball `ball x₀ ε ⊆ U`, `v` is a homeomorphism onto an open
ball `ball 0 δ_v`. Pick a small target `t ≠ 0` with both `t` and
`ω · t` (where `ω = exp(2π i / k)`) in `ball 0 δ_v`; their preimages
under `v` are distinct, lie in `ball x₀ ε ⊆ U`, and have the same `g`
value `w₀ + t^k`. -/
private lemma not_injOn_of_analyticOrderAt_ge_two
    {g : ℂ → ℂ} {x₀ w₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hne : ¬ ∀ᶠ z in 𝓝 x₀, g z = w₀)
    (hge : (2 : ℕ∞) ≤ analyticOrderAt (fun z => g z - w₀) x₀) :
    ¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U := by
  rintro ⟨U, hU_nhds, hU_inj⟩
  -- Recover `k ≥ 2` and the factorization radius.
  obtain ⟨k, hk_ge_one, hk_eq⟩ :=
    analyticOrderAt_eq_natCast_ge_one_of_not_eventually hg h_w₀ hne
  rw [hk_eq] at hge
  have hk_ge_two : 2 ≤ k := by exact_mod_cast hge
  obtain ⟨R, hR_pos, u, hu_an, hu_x₀, hfact⟩ :=
    analytic_local_factorization hk_ge_one hg h_w₀ hk_eq
  -- ZZ87 gives a `k`-th root of `u` on a small ball.
  obtain ⟨r_root, ρ', hρ'_pos, hρ'_le, hr_an, hr_pow⟩ :=
    analytic_kth_root_of_nonvanishing hR_pos hu_an hu_x₀ hk_ge_one
  -- Build `v(z) := (z - x₀) * r_root(z)`, with `v(x₀) = 0` and `deriv v x₀ = r_root x₀ ≠ 0`.
  set v : ℂ → ℂ := fun z => (z - x₀) * r_root z with hv_def
  have hv_x₀ : v x₀ = 0 := by simp [hv_def]
  -- `r_root x₀ ≠ 0` since `r_root x₀ ^ k = u x₀ ≠ 0`.
  have hr_x₀_in : x₀ ∈ Metric.closedBall x₀ ρ' := Metric.mem_closedBall_self hρ'_pos.le
  have hr_x₀_pow : r_root x₀ ^ k = u x₀ := hr_pow x₀ hr_x₀_in
  have hr_x₀_ne : r_root x₀ ≠ 0 := by
    intro h
    have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk_ge_one
    have : (0 : ℂ) ^ k = u x₀ := by rw [← h]; exact hr_x₀_pow
    rw [zero_pow hk0] at this
    exact hu_x₀ this.symm
  -- `v` is analytic on `closedBall x₀ ρ'`.
  have hv_an : AnalyticOnNhd ℂ v (Metric.closedBall x₀ ρ') := by
    intro z hz
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => ζ - x₀) z :=
      analyticAt_id.sub analyticAt_const
    have h2 : AnalyticAt ℂ r_root z := hr_an z hz
    exact h1.mul h2
  have hv_at_x₀ : AnalyticAt ℂ v x₀ := hv_an x₀ hr_x₀_in
  -- `deriv v x₀ = r_root x₀ ≠ 0` (product rule).
  have hr_root_diff : DifferentiableAt ℂ r_root x₀ :=
    (hr_an x₀ hr_x₀_in).differentiableAt
  have hsub_diff : DifferentiableAt ℂ (fun ζ : ℂ => ζ - x₀) x₀ :=
    differentiableAt_id.sub (differentiableAt_const x₀)
  have hderiv_v : deriv v x₀ = r_root x₀ := by
    have hp := deriv_mul (𝕜 := ℂ) hsub_diff hr_root_diff
    have hsub_d : deriv (fun ζ : ℂ => ζ - x₀) x₀ = 1 := by
      have hd' := deriv_sub (𝕜 := ℂ) (differentiableAt_id) (differentiableAt_const x₀)
      simp at hd'; exact hd'
    rw [hsub_d, sub_self, zero_mul, add_zero, one_mul] at hp
    exact hp
  have hderiv_v_ne : deriv v x₀ ≠ 0 := by rw [hderiv_v]; exact hr_x₀_ne
  -- Pick a small ball `ball x₀ ε_top` inside `U ∩ ball x₀ ρ'`.
  obtain ⟨ε_U, hε_U_pos, hε_U_sub_U⟩ := Metric.mem_nhds_iff.mp hU_nhds
  set ε_top : ℝ := min ε_U ρ' with hε_top_def
  have hε_top_pos : 0 < ε_top := lt_min hε_U_pos hρ'_pos
  have hε_top_le_U : ε_top ≤ ε_U := min_le_left _ _
  have hε_top_le_ρ' : ε_top ≤ ρ' := min_le_right _ _
  -- Continuity of `v` at `x₀` gives `δ_top > 0` with `ball x₀ δ_top ⊆ v⁻¹ ball 0 δ_v`...
  -- but we don't actually need it. We instead take a small `ξ` and pull back.
  -- We need to ensure the `z` returned by `hcount_v` lies in `ball x₀ ε_top`. By
  -- `hcount_v`, the unique preimage `z` lies in `ball x₀ ε_v`. To force it inside
  -- `ball x₀ ε_top`, we need to shrink δ_v. Continuity of the local inverse
  -- (`OpenPartialHomeomorph.continuousAt_symm`) at `0` gives this.
  -- Re-derive using ZZ74's statement reusing the OpenPartialHomeomorph machinery.
  have hsd_v : HasStrictDerivAt v (deriv v x₀) x₀ := hv_at_x₀.hasStrictDerivAt
  have hsfd_v :
      HasStrictFDerivAt v
        (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv v x₀) hderiv_v_ne) :
          ℂ →L[ℂ] ℂ) x₀ :=
    hsd_v.hasStrictFDerivAt_equiv hderiv_v_ne
  let ψ : OpenPartialHomeomorph ℂ ℂ := hsfd_v.toOpenPartialHomeomorph v
  have h_x0_src : x₀ ∈ ψ.source := hsfd_v.mem_toOpenPartialHomeomorph_source
  have h_v_x0_tgt : v x₀ ∈ ψ.target := hsfd_v.image_mem_toOpenPartialHomeomorph_target
  have h_coe_v : (ψ : ℂ → ℂ) = v := hsfd_v.toOpenPartialHomeomorph_coe
  -- `ψ.source` is open and contains `x₀`; ditto `ψ.target` contains `0 = v x₀`.
  have h_src_nhds : ψ.source ∈ 𝓝 x₀ := ψ.open_source.mem_nhds h_x0_src
  -- Find `s > 0` with `ball x₀ s ⊆ ψ.source ∩ ball x₀ ε_top`.
  have h_inter_nhds : ψ.source ∩ Metric.ball x₀ ε_top ∈ 𝓝 x₀ :=
    Filter.inter_mem h_src_nhds (Metric.ball_mem_nhds x₀ hε_top_pos)
  obtain ⟨s, hs_pos, hs_sub⟩ := Metric.mem_nhds_iff.mp h_inter_nhds
  -- `ψ.symm` is continuous at `v x₀ = 0`, so the preimage of `ball x₀ s` is a nbhd of `0`.
  have h_symm_cont : ContinuousAt ψ.symm (v x₀) :=
    (ψ.continuousOn_symm).continuousAt (ψ.open_target.mem_nhds h_v_x0_tgt)
  have h_symm_v_x0 : ψ.symm (v x₀) = x₀ := by
    have := ψ.left_inv h_x0_src
    have hψx₀ : (ψ : ℂ → ℂ) x₀ = v x₀ := by rw [h_coe_v]
    rw [hψx₀] at this
    exact this
  have h_pre_nhds : ψ.symm ⁻¹' Metric.ball x₀ s ∈ 𝓝 (v x₀) := by
    have htend := h_symm_cont.tendsto
    rw [h_symm_v_x0] at htend
    exact htend (Metric.ball_mem_nhds x₀ hs_pos)
  have h_combo_nhds :
      ψ.target ∩ ψ.symm ⁻¹' Metric.ball x₀ s ∈ 𝓝 (v x₀) :=
    Filter.inter_mem (ψ.open_target.mem_nhds h_v_x0_tgt) h_pre_nhds
  rw [hv_x₀] at h_combo_nhds
  obtain ⟨τ, hτ_pos, hτ_sub⟩ := Metric.mem_nhds_iff.mp h_combo_nhds
  -- For any `ξ ∈ ball 0 τ`, `ξ ∈ ψ.target` and `ψ.symm ξ ∈ ball x₀ s ⊆ ψ.source ∩ ball x₀ ε_top`.
  -- Pick a primitive `k`-th root of unity `ω = exp(2π i / k)`. With `k ≥ 2`,
  -- `ω ≠ 1`. Choose any nonzero `ξ` with `|ξ| < τ` and `|ω · ξ| < τ` (i.e. `|ξ| < τ`).
  -- Then `ψ.symm ξ` and `ψ.symm (ω · ξ)` are two distinct points in `ball x₀ ε_top ⊆ U`,
  -- each in `ψ.source`, with `v(ψ.symm ξ) = ξ` and `v(ψ.symm (ω · ξ)) = ω · ξ`.
  -- Hence `g(ψ.symm ξ) - w₀ = ξ^k` and `g(ψ.symm (ω · ξ)) - w₀ = (ω · ξ)^k = ω^k · ξ^k = ξ^k`.
  -- So they have the same `g`-value but are distinct, contradicting `InjOn g U`.
  -- Pick ξ := τ/2 (a real, nonzero, |ξ| = τ/2 < τ).
  set ξ : ℂ := (τ / 2 : ℝ) with hξ_def
  have hξ_norm : ‖ξ‖ = τ / 2 := by
    show ‖((τ / 2 : ℝ) : ℂ)‖ = τ / 2
    rw [Complex.norm_real]
    exact abs_of_pos (by linarith)
  have hξ_ne : ξ ≠ 0 := by
    intro h
    have h_norm : ‖ξ‖ = 0 := by rw [h]; simp
    rw [hξ_norm] at h_norm
    linarith
  have hξ_in : ξ ∈ Metric.ball (0 : ℂ) τ := by
    rw [Metric.mem_ball, dist_zero_right, hξ_norm]
    linarith
  -- The primitive `k`-th root of unity `ω`.
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hω_def
  have hk_ne : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk_ge_one)
  -- `ω^k = 1`.
  have hω_pow : ω ^ k = 1 := by
    rw [hω_def, ← Complex.exp_nat_mul]
    have : (k : ℂ) * (2 * Real.pi * Complex.I / k) = 2 * Real.pi * Complex.I := by
      field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  -- `ω ≠ 1`: since `k ≥ 2`.
  have hω_ne_one : ω ≠ 1 := by
    intro hcontra
    rw [hω_def, Complex.exp_eq_one_iff] at hcontra
    obtain ⟨n, hn⟩ := hcontra
    -- hn : 2 * π * I / k = n * (2 * π * I).
    -- Multiply both sides by k: 2 π i = n * 2 π i * k. Divide by 2 π i: 1 = n * k.
    have hpi_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast Real.pi_ne_zero
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero h2 hpi) Complex.I_ne_zero
    -- From `hn`, multiply by `(k : ℂ)`:
    have hn' : (2 * (Real.pi : ℂ) * Complex.I) = n * (2 * (Real.pi : ℂ) * Complex.I) * k := by
      have := congrArg (fun w => w * (k : ℂ)) hn
      simp at this
      field_simp at this
      linear_combination this
    -- Cancel `2 π i`: `1 = n * k`.
    have h_one : (1 : ℂ) = n * k := by
      have hh : (2 * (Real.pi : ℂ) * Complex.I) * 1 =
                (2 * (Real.pi : ℂ) * Complex.I) * (n * k) := by
        rw [mul_one]; rw [hn']; ring
      exact mul_left_cancel₀ hpi_ne hh
    have h_int : (n : ℤ) * (k : ℤ) = 1 := by
      have := h_one
      have h2 : (1 : ℂ) = ((n * (k : ℤ) : ℤ) : ℂ) := by push_cast; linear_combination this
      have h3 : ((1 : ℤ) : ℂ) = ((n * (k : ℤ) : ℤ) : ℂ) := by push_cast; linear_combination h2
      exact_mod_cast h3.symm
    -- From `n * k = 1` in ℤ with k ≥ 2, contradiction.
    have h_k_int : (k : ℤ) ≥ 2 := by exact_mod_cast hk_ge_two
    have h_k_pos : (1 : ℤ) ≤ k := by linarith
    -- `n * k = 1` ⟹ `k ∣ 1` ⟹ `k ≤ 1`.
    have h_dvd : (k : ℤ) ∣ 1 := ⟨n, by linarith [h_int]⟩
    have h_k_le : (k : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) h_dvd
    linarith
  -- `‖ω‖ = 1`.
  have hω_norm : ‖ω‖ = 1 := by
    rw [hω_def, Complex.norm_exp]
    have h_re_zero : (2 * (Real.pi : ℂ) * Complex.I / (k : ℂ)).re = 0 := by
      have h_num : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
      have h_num_im : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by
        simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im]
      have hk_re : ((k : ℂ)).re = (k : ℝ) := Complex.natCast_re _
      have hk_im : ((k : ℂ)).im = 0 := Complex.natCast_im _
      rw [Complex.div_re, h_num, h_num_im, hk_re, hk_im]
      have hk_norm_sq : Complex.normSq (k : ℂ) ≠ 0 := by
        apply Complex.normSq_ne_zero.mpr
        exact hk_ne
      field_simp
    rw [h_re_zero]; exact Real.exp_zero
  -- `ω · ξ ∈ ball 0 τ` (same modulus as `ξ`).
  have hωξ_norm : ‖ω * ξ‖ = τ / 2 := by
    rw [norm_mul, hω_norm, one_mul, hξ_norm]
  have hωξ_in : ω * ξ ∈ Metric.ball (0 : ℂ) τ := by
    rw [Metric.mem_ball, dist_zero_right, hωξ_norm]
    linarith
  -- Pull back via `ψ.symm`.
  have h_ξ_in_target : ξ ∈ ψ.target := (hτ_sub hξ_in).1
  have h_ωξ_in_target : ω * ξ ∈ ψ.target := (hτ_sub hωξ_in).1
  have h_z₁ : ψ.symm ξ ∈ Metric.ball x₀ s := (hτ_sub hξ_in).2
  have h_z₂ : ψ.symm (ω * ξ) ∈ Metric.ball x₀ s := (hτ_sub hωξ_in).2
  set z₁ : ℂ := ψ.symm ξ with hz₁_def
  set z₂ : ℂ := ψ.symm (ω * ξ) with hz₂_def
  -- Both `z₁, z₂ ∈ ball x₀ ε_top ∩ ψ.source`.
  have hz₁_in_top : z₁ ∈ Metric.ball x₀ ε_top := (hs_sub h_z₁).2
  have hz₂_in_top : z₂ ∈ Metric.ball x₀ ε_top := (hs_sub h_z₂).2
  have hz₁_src : z₁ ∈ ψ.source := (hs_sub h_z₁).1
  have hz₂_src : z₂ ∈ ψ.source := (hs_sub h_z₂).1
  -- `v z₁ = ξ`, `v z₂ = ω * ξ`.
  have hv_z₁ : v z₁ = ξ := by
    have : (ψ : ℂ → ℂ) (ψ.symm ξ) = ξ := ψ.right_inv h_ξ_in_target
    rw [h_coe_v] at this; exact this
  have hv_z₂ : v z₂ = ω * ξ := by
    have : (ψ : ℂ → ℂ) (ψ.symm (ω * ξ)) = ω * ξ := ψ.right_inv h_ωξ_in_target
    rw [h_coe_v] at this; exact this
  -- `g z_i - w₀ = (v z_i)^k`.
  have hz₁_close : z₁ ∈ Metric.closedBall x₀ ρ' := by
    have hz₁_in_ε_top : z₁ ∈ Metric.ball x₀ ε_top := hz₁_in_top
    rw [Metric.mem_ball] at hz₁_in_ε_top
    rw [Metric.mem_closedBall]
    linarith [hε_top_le_ρ']
  have hz₂_close : z₂ ∈ Metric.closedBall x₀ ρ' := by
    have hz₂_in_ε_top : z₂ ∈ Metric.ball x₀ ε_top := hz₂_in_top
    rw [Metric.mem_ball] at hz₂_in_ε_top
    rw [Metric.mem_closedBall]
    linarith [hε_top_le_ρ']
  have h_factor : ∀ z ∈ Metric.closedBall x₀ ρ', g z - w₀ = (v z) ^ k := by
    intro z hz
    have h1 := hr_pow z hz
    have hz_in_R : z ∈ Metric.closedBall x₀ R :=
      (Metric.closedBall_subset_closedBall hρ'_le) hz
    have h2 : g z - w₀ = (z - x₀) ^ k * u z := hfact z hz_in_R
    rw [hv_def]
    rw [show ((fun z => (z - x₀) * r_root z) z) = (z - x₀) * r_root z from rfl]
    rw [mul_pow, h1]
    exact h2
  have hg_z₁ : g z₁ - w₀ = ξ ^ k := by rw [h_factor z₁ hz₁_close, hv_z₁]
  have hg_z₂ : g z₂ - w₀ = (ω * ξ) ^ k := by rw [h_factor z₂ hz₂_close, hv_z₂]
  have h_ωξ_pow : (ω * ξ) ^ k = ξ ^ k := by
    rw [mul_pow, hω_pow, one_mul]
  have h_g_eq : g z₁ = g z₂ := by
    have h1 : g z₁ = w₀ + ξ ^ k := by linarith [hg_z₁]
    have h2 : g z₂ = w₀ + (ω * ξ) ^ k := by linarith [hg_z₂]
    rw [h1, h2, h_ωξ_pow]
  -- `z₁ ≠ z₂` because `ψ.symm` is injective on `ψ.target`, and `ξ ≠ ω · ξ`.
  have hz₁_ne_z₂ : z₁ ≠ z₂ := by
    intro h_eq
    have h_v_eq : v z₁ = v z₂ := by rw [h_eq]
    rw [hv_z₁, hv_z₂] at h_v_eq
    -- `ξ = ω * ξ` ⟹ `(1 - ω) * ξ = 0` ⟹ `ω = 1` (since `ξ ≠ 0`).
    have : (1 - ω) * ξ = 0 := by linarith [h_v_eq]
    rcases mul_eq_zero.mp this with hω_one | hξ_zero
    · apply hω_ne_one
      linarith [hω_one]
    · exact hξ_ne hξ_zero
  -- `z₁, z₂ ∈ U`.
  have hz₁_U : z₁ ∈ U := by
    apply hε_U_sub_U
    exact (Metric.ball_subset_ball hε_top_le_U) hz₁_in_top
  have hz₂_U : z₂ ∈ U := by
    apply hε_U_sub_U
    exact (Metric.ball_subset_ball hε_top_le_U) hz₂_in_top
  -- Contradiction with `InjOn g U`.
  exact hz₁_ne_z₂ (hU_inj hz₁_U hz₂_U h_g_eq)

/-- **Planar key lemma: not locally injective ↔ deriv = 0.**

For analytic `g : ℂ → ℂ` at `x₀` not eventually equal to `g x₀` near
`x₀`,

  `(¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U) ↔ deriv g x₀ = 0`. -/
theorem notInjOn_iff_deriv_zero_of_analytic
    {g : ℂ → ℂ} {x₀ : ℂ}
    (hg : AnalyticAt ℂ g x₀)
    (hne : ¬ ∀ᶠ z in 𝓝 x₀, g z = g x₀) :
    (¬ ∃ U ∈ 𝓝 x₀, Set.InjOn g U) ↔ deriv g x₀ = 0 := by
  set w₀ : ℂ := g x₀ with hw₀_def
  have h_w₀ : g x₀ = w₀ := rfl
  refine ⟨?_, ?_⟩
  · intro h_notInj
    by_contra hd_ne
    exact h_notInj (injOn_nhds_of_deriv_ne_zero hg hd_ne)
  · intro hd
    have h_ord_ge_two :
        (2 : ℕ∞) ≤ analyticOrderAt (fun z => g z - w₀) x₀ :=
      analyticOrderAt_ge_two_of_deriv_zero hg h_w₀ hne hd
    exact not_injOn_of_analyticOrderAt_ge_two hg h_w₀ hne h_ord_ge_two

/-! ## Step 4. Manifold-side bridge -/

/-- **Chart bridge package.** Records a chart-pullback view of `f̃ : X → Y`
near `x : X` together with the data needed to translate "no neighbourhood
of `x` is `InjOn` for `f̃`" into "no neighbourhood of `chartAt x x` is
`InjOn` for the chart pullback `F`", and analyticity of `F`.

Fields:

* `F : ℂ → ℂ` — the chart pullback of `f̃` near `x`,
* `z₀ : ℂ` — the chart image of `x`,
* `hF_an` — `F` is analytic at `z₀`,
* `hF_ne_const` — `F` is not eventually equal to its value at `z₀`,
* `inj_iff` — for every neighbourhood `U` of `x` in `X`, there exists a
  neighbourhood `V` of `z₀` in ℂ with `Set.InjOn (f̃) U ↔ Set.InjOn F V`.
  This is the precise content of "non-injectivity is local and transports
  along charts". -/
structure ChartBridgePackage {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x : X) where
  F : ℂ → ℂ
  z₀ : ℂ
  hF_an : AnalyticAt ℂ F z₀
  hF_ne_const : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀
  inj_iff :
    (¬ ∃ U ∈ 𝓝 x, Set.InjOn f U) ↔ ¬ ∃ V ∈ 𝓝 z₀, Set.InjOn F V

/-- **Manifold-side bridge.** Under a `ChartBridgePackage`, "`x` is in the
critical set" (no neighbourhood is `InjOn` for `f`) is equivalent to
"the chart pullback has vanishing derivative at the chart image". -/
theorem criticalSet_iff_chart_pullback_deriv_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {x : X}
    (P : ChartBridgePackage f x) :
    (¬ ∃ U ∈ 𝓝 x, Set.InjOn f U) ↔ deriv P.F P.z₀ = 0 := by
  rw [P.inj_iff]
  exact notInjOn_iff_deriv_zero_of_analytic P.hF_an P.hF_ne_const

end Manifold
end JacobianChallenge

end
