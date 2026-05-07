/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.Constructions
import JacobianChallenge.Manifold.LocalKFoldMultiplicity

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Analytic `k`-th root branch on a disc around a non-vanishing point.

This file discharges the named gap
`analytic_kth_root_branch_exists_statement` from
`LocalKFoldMultiplicity` for **every** `k ≥ 1`.

## Strategy

Let `u : ℂ → ℂ` be analytic on `closedBall x₀ ρ` with `u x₀ ≠ 0`. Set
`c₀ := u x₀`. The function `w(z) := u(z) / c₀` is analytic on the same
disc and satisfies `w x₀ = 1`. By continuity, on a small enough disc
`closedBall x₀ ρ'`, `w(z)` stays inside the open ball
`Metric.ball (1 : ℂ) (1/2)`, which is contained in `Complex.slitPlane`
(real parts stay ≥ 1/2 > 0). On `slitPlane`, `Complex.log` is analytic
and `Complex.exp ∘ Complex.log = id`. Pick any `c₀^{1/k}` via
`Complex.exp ((Complex.log c₀) / k)` and define

  `r(z) := Complex.exp ((Complex.log c₀) / k)
            * Complex.exp ((Complex.log (w z)) / k)`.

Then `r(z) ^ k = c₀ * w(z) = u(z)`.
-/

namespace JacobianChallenge

open Complex Metric

/-- Points in `Metric.ball (1 : ℂ) (1/2)` lie in `Complex.slitPlane`. -/
lemma slitPlane_of_mem_ball_one {z : ℂ} (hz : z ∈ Metric.ball (1 : ℂ) (1/2)) :
    z ∈ Complex.slitPlane := by
  -- `Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}`.
  -- We show `0 < z.re` from `|z - 1| < 1/2`.
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h_re : |z.re - 1| ≤ ‖z - 1‖ := by
    have := Complex.abs_re_le_norm (z - 1)
    simpa [Complex.sub_re] using this
  have h_re_lt : |z.re - 1| < 1/2 := lt_of_le_of_lt h_re hz
  have hpos : 0 < z.re := by
    have := abs_lt.mp h_re_lt
    linarith [this.1]
  exact Or.inl hpos

/-- **Analytic `k`-th root branch on a disc.**

If `u : ℂ → ℂ` is analytic on `closedBall x₀ ρ` and `u x₀ ≠ 0`, then for
every `k ≥ 1` there exists a smaller closed disc `closedBall x₀ ρ'`
(`0 < ρ' ≤ ρ`) and an analytic function `r : ℂ → ℂ` on that disc with
`r(z)^k = u(z)`. -/
theorem analytic_kth_root_of_nonvanishing
    {u : ℂ → ℂ} {x₀ : ℂ} {ρ : ℝ} {k : ℕ}
    (hρ : 0 < ρ)
    (hu : AnalyticOnNhd ℂ u (Metric.closedBall x₀ ρ))
    (hux₀ : u x₀ ≠ 0) (hk : 1 ≤ k) :
    ∃ (r : ℂ → ℂ) (ρ' : ℝ), 0 < ρ' ∧ ρ' ≤ ρ ∧
      AnalyticOnNhd ℂ r (Metric.closedBall x₀ ρ') ∧
      ∀ z ∈ Metric.closedBall x₀ ρ', (r z) ^ k = u z := by
  -- Set `c₀ := u x₀`, `w(z) := u(z) / c₀`. Then `w x₀ = 1`.
  set c₀ : ℂ := u x₀ with hc₀
  have hc₀_ne : c₀ ≠ 0 := hux₀
  -- `u` is continuous at `x₀` (it is analytic there).
  have hu_x₀ : AnalyticAt ℂ u x₀ := hu x₀ (Metric.mem_closedBall_self hρ.le)
  have hu_cont : ContinuousAt u x₀ := hu_x₀.continuousAt
  -- Continuity of the ratio `u(z) / c₀` at `x₀`, with value `1`.
  have hw_cont : ContinuousAt (fun z => u z / c₀) x₀ := hu_cont.div_const c₀
  have hw_x₀ : (fun z => u z / c₀) x₀ = 1 := by
    simp [hc₀, div_self hc₀_ne]
  -- Find `ρ₁ > 0` with `closedBall x₀ ρ₁` mapped into `ball 1 (1/2)` by `w`.
  have hball_open : IsOpen (Metric.ball (1 : ℂ) (1/2)) := Metric.isOpen_ball
  have h_one_mem : (1 : ℂ) ∈ Metric.ball (1 : ℂ) (1/2) := by
    simp [Metric.mem_ball]; norm_num
  have h_pre :
      ∀ᶠ z in nhds x₀, (fun z => u z / c₀) z ∈ Metric.ball (1 : ℂ) (1/2) := by
    have : (fun z => u z / c₀) x₀ ∈ Metric.ball (1 : ℂ) (1/2) := by
      rw [hw_x₀]; exact h_one_mem
    exact hw_cont.eventually_mem (hball_open.mem_nhds (by rw [hw_x₀]; exact h_one_mem))
  -- Extract a metric radius from the eventually-statement.
  rw [Metric.eventually_nhds_iff] at h_pre
  obtain ⟨ε, hε_pos, hε⟩ := h_pre
  -- Use `ρ' := min (ρ/2) (ε/2)`.
  set ρ' : ℝ := min (ρ/2) (ε/2) with hρ'_def
  have hρ'_pos : 0 < ρ' := by
    apply lt_min
    · linarith
    · linarith
  have hρ'_le : ρ' ≤ ρ := by
    have : ρ' ≤ ρ/2 := min_le_left _ _
    linarith
  have hρ'_lt_ε : ρ' < ε := by
    have : ρ' ≤ ε/2 := min_le_right _ _
    linarith
  -- For `z ∈ closedBall x₀ ρ'`, we have `dist z x₀ ≤ ρ' < ε`, so the eventually
  -- condition holds, i.e. `u z / c₀ ∈ ball 1 (1/2)`.
  have hz_in_ε : ∀ z ∈ Metric.closedBall x₀ ρ',
      u z / c₀ ∈ Metric.ball (1 : ℂ) (1/2) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    have hdist : dist z x₀ < ε := lt_of_le_of_lt hz hρ'_lt_ε
    exact hε hdist
  -- Also `closedBall x₀ ρ' ⊆ closedBall x₀ ρ` so `u` analytic there.
  have hsubset : Metric.closedBall x₀ ρ' ⊆ Metric.closedBall x₀ ρ :=
    Metric.closedBall_subset_closedBall hρ'_le
  -- The analytic `k`-th root: r(z) := exp((log c₀)/k) * exp((log (u z / c₀))/k).
  let cConst : ℂ := Complex.exp ((Complex.log c₀) / k)
  let r : ℂ → ℂ := fun z => cConst * Complex.exp ((Complex.log (u z / c₀)) / k)
  refine ⟨r, ρ', hρ'_pos, hρ'_le, ?_, ?_⟩
  · -- analyticity of r on `closedBall x₀ ρ'`
    intro z hz
    have hwz : u z / c₀ ∈ Complex.slitPlane :=
      slitPlane_of_mem_ball_one (hz_in_ε z hz)
    have hu_an : AnalyticAt ℂ u z := hu z (hsubset hz)
    have hw_an : AnalyticAt ℂ (fun ζ => u ζ / c₀) z := hu_an.div_const c₀
    have hlog_an : AnalyticAt ℂ Complex.log (u z / c₀) :=
      Complex.analyticAt_log hwz
    have hcomp : AnalyticAt ℂ (fun ζ => Complex.log (u ζ / c₀)) z :=
      hlog_an.comp hw_an
    have hdiv_an : AnalyticAt ℂ (fun ζ => Complex.log (u ζ / c₀) / k) z :=
      hcomp.div_const _
    have hexp_an : AnalyticAt ℂ
        (fun ζ => Complex.exp (Complex.log (u ζ / c₀) / k)) z :=
      Complex.analyticAt_exp.comp hdiv_an
    exact analyticAt_const.mul hexp_an
  · -- pointwise equation r(z)^k = u(z)
    intro z hz
    have hwz : u z / c₀ ∈ Complex.slitPlane :=
      slitPlane_of_mem_ball_one (hz_in_ε z hz)
    have hwz_ne : u z / c₀ ≠ 0 := Complex.slitPlane_ne_zero hwz
    -- Compute r z ^ k.
    have hk_ne : (k : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
    -- `cConst ^ k = exp(log c₀)`
    have hcConst_pow :
        (Complex.exp ((Complex.log c₀) / k)) ^ k = Complex.exp (Complex.log c₀) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      field_simp
    -- `exp((log w)/k) ^ k = exp(log w)` for w := u z / c₀
    have hexp_pow :
        (Complex.exp ((Complex.log (u z / c₀)) / k)) ^ k
            = Complex.exp (Complex.log (u z / c₀)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      field_simp
    show (Complex.exp ((Complex.log c₀) / k)
           * Complex.exp ((Complex.log (u z / c₀)) / k)) ^ k = u z
    rw [mul_pow, hcConst_pow, hexp_pow]
    rw [Complex.exp_log hc₀_ne, Complex.exp_log hwz_ne]
    field_simp

/-- **Discharge of the named gap.**

The theorem `analytic_kth_root_of_nonvanishing` directly proves
`analytic_kth_root_branch_exists_statement`. -/
theorem analytic_kth_root_branch_exists
    (u : ℂ → ℂ) (x₀ : ℂ) (ρ : ℝ) (k : ℕ) (hρ : 0 < ρ) :
    analytic_kth_root_branch_exists_statement u x₀ ρ k := by
  intro hu hux₀ hk
  exact analytic_kth_root_of_nonvanishing hρ hu hux₀ hk

end JacobianChallenge
