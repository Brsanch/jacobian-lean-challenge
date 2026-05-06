/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LogDiffAnchored
import JacobianChallenge.Manifold.LogDiffAnchoredDischarge
import JacobianChallenge.Manifold.LocalNormalForm
import Mathlib.Analysis.Meromorphic.Order

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Witness for the anchored Laurent hypothesis

This file produces an unconditional witness for
`MeromorphicNonzero.LogDerivResiduePlusAnalyticAnchored f x` (defined in
`LogDiffAnchored.lean`), under the standard non-degeneracy hypothesis
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`. Combined with
`logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic` (Y1's
half-bundle real discharge), this turns the anchored chart-circle integral
identity `chartCircleIntegralAnchored f x r = ((order : ℤ) : ℂ)` into an
**unconditional** theorem.

## Strategy

For `f : MeromorphicNonzero X` and `x : X` with finite chart-pullback order,
mathlib's `meromorphicOrderAt_eq_int_iff` (applied to the chart pullback
`F := f.toFun ∘ (chartAt ℂ x).symm` at `z₀ := (chartAt ℂ x) x`) delivers
analytic `g : ℂ → ℂ` with `g(z₀) ≠ 0` and the local factorisation
`F(z) = (z - z₀)^k · g(z)` on the punctured-deleted-neighborhood
`𝓝[≠] z₀`. Differentiating under that factorisation and dividing by `F`,

  `F'(z) / F(z) = k / (z - z₀) + g'(z) / g(z)`

with the analytic-on-a-disk remainder `h := g'/g` (analytic because `g(z₀) ≠ 0`
implies `g ≠ 0` on a neighborhood, and quotient of analytic functions with
nonvanishing denominator is analytic).

For sufficiently small `r > 0`, the chart-circle of radius `r` centred at `z₀`
sits inside both the chart target (so `circleParameter` is well-defined) and
inside the punctured-deleted-neighborhood from mathlib's factorisation, giving
the right Laurent shape on the entire chart-circle.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature changed (pure addition).
* The witness is delivered through the existing
  `LogDerivResiduePlusAnalyticAnchored` definition shape (matches Y1).
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex Filter Set

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Commit Z1.A — planar Laurent factorisation of `f.toFun ∘ chart.symm`

Wire `f.meromorphic` (manifold meromorphy on the universe) to the planar
`MeromorphicAt _ z₀` for the chart pullback `f.toFun ∘ (chartAt ℂ x).symm`,
and apply mathlib's `meromorphicOrderAt_eq_int_iff` to extract the integer
`k = orderFun 𝓘(ℂ,ℂ) f.toFun x` together with an analytic factor `g`.

This packages the **planar** content delivered by mathlib at the chart-image
basepoint `z₀ := (chartAt ℂ x) x`. -/

/-- **Planar Laurent factorisation of the chart pullback.**

Under the standard non-degeneracy hypothesis
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`, the chart pullback
`F := f.toFun ∘ (chartAt ℂ x).symm` admits the local factorisation
`F(z) = (z - z₀)^k · g(z)` for some analytic `g` with `g(z₀) ≠ 0`, on the
punctured-deleted-neighborhood `𝓝[≠] z₀`, where `k` is the integer
`orderFun 𝓘(ℂ,ℂ) f.toFun x` (cast through the standard
`mmeromorphicOrderAt.untop₀` round-trip).

This is the planar content from mathlib's `meromorphicOrderAt_eq_int_iff`
specialised to the chart-pulled-back representative. -/
lemma planar_laurent_factorization
    (f : MeromorphicNonzero X) (x : X)
    (hf0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤) :
    ∃ (g : ℂ → ℂ),
      AnalyticAt ℂ g ((chartAt ℂ x) x) ∧
      g ((chartAt ℂ x) x) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
        (f.toFun ∘ (chartAt ℂ x).symm) z =
          (z - (chartAt ℂ x) x) ^
              (MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) • g z := by
  -- The manifold-meromorphy of `f.toFun` at `x` is, by definition, planar
  -- meromorphy of `F := f.toFun ∘ (chartAt ℂ x).symm` at `z₀ := (chartAt ℂ x) x`.
  have hf_at : MMeromorphicAt (𝓘(ℂ, ℂ)) f.toFun x := f.meromorphic x trivial
  -- `MMeromorphicAt.exists_local_normal_form` (in `LocalNormalForm.lean`)
  -- packages `meromorphicOrderAt_eq_int_iff` for us, at the cost of producing
  -- the factorisation indexed by `localOrder = orderFun`.
  have h := hf_at.exists_local_normal_form hf0
  -- `localOrder I f.toFun x = MMeromorphicOn.orderFun I f.toFun x` is `rfl`.
  exact h

/-! ## Commit Z1.B — log-derivative of the planar factorisation

For the analytic factor `g` with `g(z₀) ≠ 0` produced by Z1.A, the
log-derivative of the product `z ↦ (z - z₀)^k · g(z)` decomposes as
`k / (z - z₀) + g'(z) / g(z)` at any point `z ≠ z₀` where `g(z) ≠ 0`.

This is the "differentiate the factorisation" step. The derivative product
rule gives
`deriv ((·-z₀)^k · g) z = k·(z-z₀)^(k-1)·g(z) + (z-z₀)^k·g'(z)`,
and dividing by the value `(z-z₀)^k · g(z)` produces the simple-pole +
analytic-quotient decomposition. -/

/-- **Log-derivative of `(·-z₀)^k · g`, pointwise.** For `z ≠ z₀` with
`g(z) ≠ 0` and `g` differentiable at `z`,
`(d/dz)((·-z₀)^k · g) z / ((z-z₀)^k · g(z)) = k/(z-z₀) + g'(z)/g(z)`.

This is the local pointwise log-derivative formula at the level of
ordinary planar derivatives in `ℂ`. -/
lemma logDeriv_zpow_smul_pointwise
    (k : ℤ) (z₀ : ℂ) (g : ℂ → ℂ) {z : ℂ}
    (hz : z ≠ z₀) (hg : DifferentiableAt ℂ g z) (hgz : g z ≠ 0) :
    deriv (fun w => (w - z₀) ^ k * g w) z /
        ((z - z₀) ^ k * g z) =
      (k : ℂ) / (z - z₀) + deriv g z / g z := by
  have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  have hpow_val : (z - z₀) ^ k ≠ 0 := zpow_ne_zero k hsub
  -- Use `HasDerivAt` machinery throughout.
  -- `HasDerivAt (fun w => w - z₀) 1 z`.
  have hsubAt : HasDerivAt (fun w : ℂ => w - z₀) 1 z :=
    (hasDerivAt_id z).sub_const z₀
  -- `HasDerivAt (fun u => u^k) (k * (z-z₀)^(k-1)) (z - z₀)` via mathlib lemma.
  have hzpowAt : HasDerivAt (fun u : ℂ => u ^ k)
      ((k : ℂ) * (z - z₀) ^ (k - 1)) (z - z₀) :=
    hasDerivAt_zpow k (z - z₀) (Or.inl hsub)
  -- Composition: `HasDerivAt (fun w => (w - z₀)^k) (k * (z-z₀)^(k-1) * 1) z`.
  have hpowAt0 :
      HasDerivAt ((fun u : ℂ => u ^ k) ∘ (fun w : ℂ => w - z₀))
        ((k : ℂ) * (z - z₀) ^ (k - 1) * 1) z :=
    hzpowAt.comp z hsubAt
  have hpowAt :
      HasDerivAt (fun w : ℂ => (w - z₀) ^ k)
        ((k : ℂ) * (z - z₀) ^ (k - 1)) z := by
    have h_eq_comp : (fun u : ℂ => u ^ k) ∘ (fun w : ℂ => w - z₀)
        = (fun w : ℂ => (w - z₀) ^ k) := rfl
    rw [h_eq_comp] at hpowAt0
    simpa using hpowAt0
  -- Now product rule via `HasDerivAt.mul`.
  have hgAt : HasDerivAt g (deriv g z) z := hg.hasDerivAt
  have hprodAt :
      HasDerivAt (fun w : ℂ => (w - z₀) ^ k * g w)
        ((k : ℂ) * (z - z₀) ^ (k - 1) * g z + (z - z₀) ^ k * deriv g z) z :=
    hpowAt.mul hgAt
  have hprod :
      deriv (fun w : ℂ => (w - z₀) ^ k * g w) z
        = (k : ℂ) * (z - z₀) ^ (k - 1) * g z + (z - z₀) ^ k * deriv g z :=
    hprodAt.deriv
  rw [hprod, add_div]
  congr 1
  · -- `(k * (z-z₀)^(k-1) * g z) / ((z-z₀)^k * g z) = k / (z-z₀)`.
    rw [mul_div_mul_right _ _ hgz]
    -- `(z - z₀)^k = (z - z₀)^(k-1) * (z - z₀)`.
    have hzpow_split : (z - z₀) ^ k = (z - z₀) ^ (k - 1) * (z - z₀) := by
      have h := zpow_add_one₀ hsub (k - 1)
      -- h : (z - z₀) ^ (k - 1 + 1) = (z - z₀) ^ (k - 1) * (z - z₀)
      have : k - 1 + 1 = k := by ring
      rw [this] at h
      exact h
    rw [hzpow_split, ← div_div, mul_div_assoc,
      div_self (zpow_ne_zero (k - 1) hsub), mul_one]
  · rw [mul_div_mul_left _ _ hpow_val]

/-! ## Commit Z1.C — radius extraction

Combine the four small-`r` witnesses (chart-target containment,
Z1.A factorisation on `𝓝[≠] z₀`, `g ≠ 0` on a closed disk, `g'/g` analytic
on a neighborhood of the closed disk) into a single positive radius
`r > 0` on which all four hold simultaneously. -/

/-- **Radius extraction.** Given the analytic factor `g` from Z1.A
(`g(z₀) ≠ 0`, factorisation on `𝓝[≠] z₀`) and the chart at `x`, there is a
common positive radius `r > 0` such that:

* the closed ball `closedBall z₀ r` is contained in the chart target,
* `g ≠ 0` on the closed ball,
* `g` is analytic on a neighborhood of the closed ball,
* the factorisation holds on the punctured open ball.

This is the "small enough `r`" packaging consumed by Z1.D. -/
lemma extract_common_radius
    (f : MeromorphicNonzero X) (x : X) (k : ℤ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g ((chartAt ℂ x) x))
    (hg_ne : g ((chartAt ℂ x) x) ≠ 0)
    (h_fact : ∀ᶠ z in 𝓝[≠] ((chartAt ℂ x) x),
      (f.toFun ∘ (chartAt ℂ x).symm) z =
        (z - (chartAt ℂ x) x) ^ k • g z) :
    ∃ (r R : ℝ), 0 < r ∧ r < R ∧
      Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target ∧
      (∀ z ∈ Metric.closedBall ((chartAt ℂ x) x) r, g z ≠ 0) ∧
      AnalyticOnNhd ℂ g (Metric.closedBall ((chartAt ℂ x) x) r) ∧
      Metric.closedBall ((chartAt ℂ x) x) r ⊆ Metric.ball ((chartAt ℂ x) x) R ∧
      (∀ z ∈ Metric.ball ((chartAt ℂ x) x) R,
        z ≠ (chartAt ℂ x) x →
          (f.toFun ∘ (chartAt ℂ x).symm) z =
            (z - (chartAt ℂ x) x) ^ k • g z) := by
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- (1) Chart target is open and contains `z₀`.
  have h_z0_target : z₀ ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  obtain ⟨r₁, hr₁_pos, hr₁_sub⟩ :=
    Metric.isOpen_iff.mp (chartAt ℂ x).open_target z₀ h_z0_target
  -- (2) `g` analytic on a neighborhood of `z₀`: extract a radius via
  -- `AnalyticAt.eventually_analyticAt`.
  have h_ev_an : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg_an.eventually_analyticAt
  obtain ⟨r₂, hr₂_pos, hr₂_sub⟩ := Metric.eventually_nhds_iff.mp h_ev_an
  -- (3) `g ≠ 0` on a neighborhood: continuity of `g` plus `g(z₀) ≠ 0`.
  have hg_cont : ContinuousAt g z₀ := hg_an.continuousAt
  have h_ne_nhds : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg_cont.eventually_ne hg_ne
  obtain ⟨r₃, hr₃_pos, hr₃_sub⟩ := Metric.eventually_nhds_iff.mp h_ne_nhds
  -- (4) Factorisation on a punctured neighborhood: extract a radius.
  -- Convert `∀ᶠ z in 𝓝[≠] z₀, P z` to `∀ᶠ z in 𝓝 z₀, z ≠ z₀ → P z`.
  have h_fact' : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ →
      (f.toFun ∘ (chartAt ℂ x).symm) z =
        (z - z₀) ^ k • g z := by
    rw [eventually_nhdsWithin_iff] at h_fact
    -- `h_fact : ∀ᶠ z in 𝓝 z₀, z ∈ {z₀}ᶜ → P z`.
    filter_upwards [h_fact] with z hz hzne
    exact hz hzne
  obtain ⟨r₄, hr₄_pos, hr₄_eq⟩ := Metric.eventually_nhds_iff.mp h_fact'
  -- Pick the minimum, scaled down to be a *closed* sub-radius.
  set r : ℝ := min (r₁ / 2) (min (r₂ / 2) (min (r₃ / 2) (r₄ / 2))) with hr_def
  have hr_pos : 0 < r := by
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))
    · exact half_pos hr₁_pos
    · exact half_pos hr₂_pos
    · exact half_pos hr₃_pos
    · exact half_pos hr₄_pos
  have hr_le_1 : r ≤ r₁ / 2 := by exact min_le_left _ _
  have hr_le_2 : r ≤ r₂ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_3 : r ≤ r₃ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_le_4 : r ≤ r₄ / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- Bounds: closed ball of radius r ⊆ ball of radius (r + ε) ⊆ each rᵢ-ball.
  have h1_closed : Metric.closedBall z₀ r ⊆ (chartAt ℂ x).target := by
    intro z hz
    apply hr₁_sub
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : r < r₁ := by
      calc r ≤ r₁ / 2 := hr_le_1
        _ < r₁ := by linarith
    exact lt_of_le_of_lt hz this
  have h_closed_sub_r₂ : Metric.closedBall z₀ r ⊆ Metric.ball z₀ r₂ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : r < r₂ := by
      calc r ≤ r₂ / 2 := hr_le_2
        _ < r₂ := by linarith
    exact lt_of_le_of_lt hz this
  have h_closed_sub_r₃ : Metric.closedBall z₀ r ⊆ Metric.ball z₀ r₃ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : r < r₃ := by
      calc r ≤ r₃ / 2 := hr_le_3
        _ < r₃ := by linarith
    exact lt_of_le_of_lt hz this
  have h_open_sub_r₄ : Metric.ball z₀ r ⊆ Metric.ball z₀ r₄ := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    have : r < r₄ := by
      calc r ≤ r₄ / 2 := hr_le_4
        _ < r₄ := by linarith
    exact lt_trans hz this
  -- Closed ball of radius `r` is contained in the open ball of radius `r₄`.
  have h_closed_sub_r₄_open : Metric.closedBall z₀ r ⊆ Metric.ball z₀ r₄ := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : r < r₄ := by
      calc r ≤ r₄ / 2 := hr_le_4
        _ < r₄ := by linarith
    exact lt_of_le_of_lt hz this
  refine ⟨r, r₄, hr_pos, ?_, h1_closed, ?_, ?_, h_closed_sub_r₄_open, ?_⟩
  · -- `r < r₄` for the strict containment.
    calc r ≤ r₄ / 2 := hr_le_4
      _ < r₄ := by linarith
  · -- `g ≠ 0` on closed ball.
    intro z hz
    exact hr₃_sub (h_closed_sub_r₃ hz)
  · -- `g` analytic on neighborhood of closed ball.
    intro z hz
    have hz_in_r₂ : dist z z₀ < r₂ := h_closed_sub_r₂ hz
    exact hr₂_sub hz_in_r₂
  · -- factorisation on punctured open ball of radius `r₄`.
    intro z hz hzne
    rw [Metric.mem_ball] at hz
    exact hr₄_eq hz hzne

/-! ## Commit Z1.D + Z1.E — assemble and deliver the witness

Final result: `LogDerivResiduePlusAnalyticAnchored f x` is unconditionally
witnessed under `mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`. The witness
combines Z1.A (planar Laurent factorisation) + Z1.B (log-derivative formula)
+ Z1.C (common-radius extraction). -/

/-- **Final witness for the anchored Laurent hypothesis.**

Under the standard non-degeneracy hypothesis
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x ≠ ⊤`, the right-shape
simple-pole + analytic-remainder Laurent decomposition of the
chart-anchored coefficient `logDiffCoeffAt f x` holds on a sufficiently
small chart-circle around `x`.

Combined with `logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`
(`LogDiffAnchoredDischarge.lean`, Y1's half-bundle real discharge), this
makes `chartCircleIntegralAnchored f x r = ((order : ℤ) : ℂ)` an
**unconditional** theorem (for some small `r > 0`). -/
theorem logDerivResiduePlusAnalyticAnchored_holds
    (f : MeromorphicNonzero X) (x : X)
    (hf0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x ≠ ⊤) :
    LogDerivResiduePlusAnalyticAnchored f x := by
  -- Step 1: Z1.A — planar Laurent factorisation.
  obtain ⟨g, hg_an, hg_ne, h_fact⟩ := planar_laurent_factorization f x hf0
  set k : ℤ := (MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) with hk_def
  -- Step 2: Z1.C — extract common radius `r` and outer ball radius `R`.
  obtain ⟨r, R, hr_pos, hrR, h_target_sub, hg_ne_disk, hg_an_on,
         h_closed_sub_R, h_fact_R⟩ :=
    extract_common_radius f x k g hg_an hg_ne h_fact
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  -- The analytic quotient `deriv g / g` on the closed ball.
  have hg_deriv : AnalyticOnNhd ℂ (deriv g) (Metric.closedBall z₀ r) :=
    hg_an_on.deriv
  have hquot : AnalyticOnNhd ℂ (fun z => deriv g z / g z)
      (Metric.closedBall z₀ r) := by
    intro z hz
    exact (hg_deriv z hz).div (hg_an_on z hz) (hg_ne_disk z hz)
  -- Choose `h := deriv g / g`.
  refine ⟨r, hr_pos, fun z => deriv g z / g z, hquot.continuousOn, ?_, ?_, ?_⟩
  · -- DifferentiableOn h (ball z₀ r).
    intro z hz
    exact ((hquot z (Metric.ball_subset_closedBall hz)).differentiableAt).differentiableWithinAt
  · -- Chart-target containment for every chart-circle point.
    intro θ
    apply h_target_sub
    rw [Metric.mem_closedBall]
    have h_norm_eq :
        dist (z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) z₀ = r := by
      rw [dist_eq_norm]
      ring_nf
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [abs_of_pos hr_pos]
    rw [h_norm_eq]
  · -- The Laurent identity at every chart-circle point.
    intro θ
    set z : ℂ := z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) with hz_def
    have hz_sub : z - z₀ = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [hz_def]; ring
    have hexp_ne : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hr_complex_ne : (r : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hr_pos)
    have hsub_ne : z - z₀ ≠ 0 := by
      rw [hz_sub]; exact mul_ne_zero hr_complex_ne hexp_ne
    have hz_ne : z ≠ z₀ := by
      intro hzeq
      have : z - z₀ = 0 := by rw [hzeq, sub_self]
      exact hsub_ne this
    have hz_dist : dist z z₀ = r := by
      rw [dist_eq_norm, hz_sub]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp [abs_of_pos hr_pos]
    have hz_in_closed : z ∈ Metric.closedBall z₀ r := by
      rw [Metric.mem_closedBall]; exact le_of_eq hz_dist
    have hz_target : z ∈ (chartAt ℂ x).target := h_target_sub hz_in_closed
    -- `g z ≠ 0` and `AnalyticAt g z` from Z1.C outputs.
    have hgz_ne : g z ≠ 0 := hg_ne_disk z hz_in_closed
    have hg_at_z : AnalyticAt ℂ g z := hg_an_on z hz_in_closed
    have hg_diff_z : DifferentiableAt ℂ g z := hg_at_z.differentiableAt
    -- `f.toFun ∘ chart.symm` agrees with `(·-z₀)^k * g(·)` on `Metric.ball z₀ R \ {z₀}`,
    -- which is open and contains `z` (since `dist z z₀ = r < R` and `z ≠ z₀`).
    have hz_in_R : z ∈ Metric.ball z₀ R := h_closed_sub_R hz_in_closed
    -- Build a neighborhood `U` of `z` on which the factorisation holds.
    have h_compl_open : IsOpen ({z₀}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hz_in_compl : z ∈ ({z₀}ᶜ : Set ℂ) := hz_ne
    have hU_open : IsOpen (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) :=
      Metric.isOpen_ball.inter h_compl_open
    have hz_in_U : z ∈ Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ) := ⟨hz_in_R, hz_in_compl⟩
    -- `EventuallyEq` on `𝓝 z` between `f.toFun ∘ chart.symm` and the factorisation.
    have h_eqOn :
        Set.EqOn (f.toFun ∘ (chartAt ℂ x).symm)
          (fun w : ℂ => (w - z₀) ^ k * g w)
          (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) := by
      intro w hw
      have hw_R : w ∈ Metric.ball z₀ R := hw.1
      have hw_ne : w ≠ z₀ := hw.2
      have := h_fact_R w hw_R hw_ne
      -- `•` on `ℂ → ℂ` is `*`.
      simpa [smul_eq_mul] using this
    have h_evEq : (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
        (fun w => (w - z₀) ^ k * g w) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hU_open.mem_nhds hz_in_U, h_eqOn⟩
    -- Therefore the derivative of `f.toFun ∘ chart.symm` at `z` equals the derivative
    -- of `(·-z₀)^k * g(·)` at `z`.
    have h_deriv_eq :
        deriv (f.toFun ∘ (chartAt ℂ x).symm) z =
          deriv (fun w : ℂ => (w - z₀) ^ k * g w) z := by
      exact h_evEq.deriv_eq
    -- Compute `f.toFun y = (z - z₀)^k * g(z)` for `y = circleParameter x r θ`.
    have h_chart_inv : (chartAt ℂ x) (circleParameter (X := X) x r θ) = z := by
      unfold circleParameter
      rw [(chartAt ℂ x).right_inv hz_target]
    have h_F_at_z : (f.toFun ∘ (chartAt ℂ x).symm) z =
        (z - z₀) ^ k * g z := by
      have := h_fact_R z hz_in_R hz_ne
      simpa [smul_eq_mul] using this
    -- `f.toFun (circleParameter x r θ) = (f.toFun ∘ chart.symm) z`.
    have h_f_eq : f.toFun (circleParameter (X := X) x r θ) =
        (f.toFun ∘ (chartAt ℂ x).symm) z := by
      unfold circleParameter
      rfl
    -- Now compute `logDiffCoeffAt f x (circleParameter x r θ)`.
    rw [logDiffCoeffAt_circleParameter f x r θ hz_target]
    -- Goal: `deriv (f.toFun ∘ chart.symm) z / f.toFun (circleParameter x r θ)
    --        = k * (r·exp(Iθ))⁻¹ + (deriv g / g) z`.
    rw [h_f_eq, h_F_at_z, h_deriv_eq]
    -- LHS: `deriv ((·-z₀)^k * g(·)) z / ((z - z₀)^k * g z)`.
    -- By Z1.B, this equals `k/(z-z₀) + deriv g z / g z`.
    have hZB := logDeriv_zpow_smul_pointwise k z₀ g hz_ne hg_diff_z hgz_ne
    rw [hZB]
    -- Goal: `(k : ℂ)/(z - z₀) + deriv g z / g z
    --       = (k : ℂ) * (r·exp(Iθ))⁻¹ + (deriv g / g) z`.
    rw [hz_sub, div_eq_mul_inv]

end MeromorphicNonzero

end JacobianChallenge

end
