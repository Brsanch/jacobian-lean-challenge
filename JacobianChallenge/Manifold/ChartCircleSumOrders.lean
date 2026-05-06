/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartCircleSumZero
import JacobianChallenge.Manifold.ChartCircleAnchoredAllRadii
import JacobianChallenge.Manifold.ChartDiskRegularity

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # `chartCircleSum` equals the sum of integer orders, on regular chart-disks (ZZ10)

This file ships ZZ10's headline deliverable: under per-point regular
chart-disk hypotheses (ZZ9), the chart-circle sum equals the sum of
integer orders.

```
theorem chartCircleSum_eq_sum_orders
    (f : MeromorphicNonzero X)
    (S : Finset X) (r : X → ℝ)
    (hreg : ∀ x ∈ S, IsRegularChartDiskAround f x (r x))
    (hr_pos : ∀ x ∈ S, 0 < r x) :
    chartCircleSum f S r =
      ∑ x ∈ S,
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ)
```

## Strategy

The per-point identity is

```
chartCircleIntegralAnchored f x r =
  ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ)
```

at the caller's radius `r`, given `IsRegularChartDiskAround f x r` and
`0 < r`. The proof applies
`chartCircleIntegralOfFun_of_residue_plus_analytic`
(`Manifold/LogDiffAnchoredDischarge.lean`) directly with the user's
radius `r` and the analytic remainder `h(z) := deriv g z / g z`, where
`g` is the analytic non-vanishing factor in `IsRegularChartDiskAround`.
The Laurent identity at every chart-circle point of radius `r` is
**identical to the inner-radius leg** of ZZ9's
`isRegularOnAnnulus_of_isRegularChartDiskAround`; the same computation
is reused here.

The key observation: `chartCircleIntegralOfFun_of_residue_plus_analytic`
takes the radius `r` as a **parameter**, not as an existential. So
plugging in the user's `r` directly avoids the existential-radius
problem of Z1+Y1's
`logDiffAt_chartCircleIntegral_eq_order_of_residue_plus_analytic`.

The headline theorem then composes the per-point identity over `S` via
`Finset.sum_congr`.

## Anti-cheat

* No `axiom`, no `sorry`.
* No existing definition or signature is changed; this is a pure addition.
* The proof composes only previously landed unconditional theorems
  (`chartCircleIntegralOfFun_of_residue_plus_analytic` from
  `LogDiffAnchoredDischarge.lean`, `logDeriv_zpow_smul_pointwise` from
  `LogDiffAnchoredWitness.lean`, and the formal sum from
  `ChartCircleSumZero.lean`).
-/

noncomputable section

open scoped Real Topology BigOperators Manifold ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Per-point chart-circle integral identity.**

If `IsRegularChartDiskAround f x r` and `0 < r`, then the chart-anchored
circle integral at radius `r` equals the integer order of `f` at `x`,
cast to `ℂ`. -/
theorem chartCircleIntegralAnchored_eq_order_of_isRegularChartDiskAround
    (f : MeromorphicNonzero X) (x : X) (r : ℝ)
    (hr_pos : 0 < r)
    (hreg : IsRegularChartDiskAround f x r) :
    chartCircleIntegralAnchored f x r =
      ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  obtain ⟨R, g, hrR, h_target, hg_an, hg_ne, h_fact⟩ := hreg
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  set k : ℤ := (MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) with hk_def
  set kC : ℂ := (k : ℂ) with hkC
  -- closedBall r ⊆ ball R because r < R.
  have h_closed_sub_R : Metric.closedBall z₀ r ⊆ Metric.ball z₀ R := by
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  -- The analytic quotient `deriv g / g` on the closed ball.
  have hg_deriv : AnalyticOnNhd ℂ (deriv g) (Metric.closedBall z₀ r) :=
    hg_an.deriv
  have hquot : AnalyticOnNhd ℂ (fun z => deriv g z / g z)
      (Metric.closedBall z₀ r) := by
    intro z hz
    exact (hg_deriv z hz).div (hg_an z hz) (hg_ne z hz)
  -- Apply `chartCircleIntegralOfFun_of_residue_plus_analytic` directly.
  unfold chartCircleIntegralAnchored
  refine chartCircleIntegralOfFun_of_residue_plus_analytic
    (logDiffCoeffAt f x) x r hr_pos kC
    (fun z => deriv g z / g z)
    hquot.continuousOn
    (fun z hz =>
      ((hquot z (Metric.ball_subset_closedBall hz)).differentiableAt).differentiableWithinAt)
    ?_
  -- The Laurent identity at every chart-circle point of radius `r`.
  intro θ
  set z : ℂ := z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) with hz_def
  have hz_sub : z - z₀ = (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
    rw [hz_def]; ring
  have hexp_ne : Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hr_complex_ne : (r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hr_pos)
  have hsub_ne : z - z₀ ≠ 0 := by
    rw [hz_sub]; exact mul_ne_zero hr_complex_ne hexp_ne
  have hz_ne : z ≠ z₀ := fun heq => hsub_ne (by rw [heq, sub_self])
  have hz_dist : dist z z₀ = r := by
    rw [dist_eq_norm, hz_sub]
    have hcomm : Complex.exp (Complex.I * (θ : ℂ))
        = Complex.exp ((θ : ℂ) * Complex.I) := by rw [mul_comm]
    rw [hcomm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    simp [abs_of_pos hr_pos]
  have hz_in_closed : z ∈ Metric.closedBall z₀ r := by
    rw [Metric.mem_closedBall]; exact le_of_eq hz_dist
  have hz_target : z ∈ (chartAt ℂ x).target := h_target hz_in_closed
  have hgz_ne : g z ≠ 0 := hg_ne z hz_in_closed
  have hg_at_z : AnalyticAt ℂ g z := hg_an z hz_in_closed
  have hg_diff_z : DifferentiableAt ℂ g z := hg_at_z.differentiableAt
  have hz_in_R : z ∈ Metric.ball z₀ R := h_closed_sub_R hz_in_closed
  -- Show `f.toFun ∘ chart.symm` agrees with `(·-z₀)^k * g(·)` near `z`.
  have h_compl_open : IsOpen ({z₀}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hz_in_compl : z ∈ ({z₀}ᶜ : Set ℂ) := hz_ne
  have hU_open : IsOpen (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) :=
    Metric.isOpen_ball.inter h_compl_open
  have hz_in_U : z ∈ Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ) :=
    ⟨hz_in_R, hz_in_compl⟩
  have h_eqOn :
      Set.EqOn (f.toFun ∘ (chartAt ℂ x).symm)
        (fun w : ℂ => (w - z₀) ^ k * g w)
        (Metric.ball z₀ R ∩ ({z₀}ᶜ : Set ℂ)) := by
    intro w hw
    have := h_fact w hw.1 hw.2
    simpa [smul_eq_mul] using this
  have h_evEq : (f.toFun ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
      (fun w => (w - z₀) ^ k * g w) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, hU_open.mem_nhds hz_in_U, h_eqOn⟩
  have h_deriv_eq :
      deriv (f.toFun ∘ (chartAt ℂ x).symm) z =
        deriv (fun w : ℂ => (w - z₀) ^ k * g w) z := h_evEq.deriv_eq
  have h_F_at_z : (f.toFun ∘ (chartAt ℂ x).symm) z =
      (z - z₀) ^ k * g z := by
    simpa [smul_eq_mul] using h_fact z hz_in_R hz_ne
  have h_f_eq : f.toFun (circleParameter (X := X) x r θ) =
      (f.toFun ∘ (chartAt ℂ x).symm) z := by
    unfold circleParameter
    rfl
  -- Goal (after the `refine`) is the Laurent identity:
  --   logDiffCoeffAt f x (chart.symm z) = kC * (r·exp(Iθ))⁻¹ + (deriv g / g) z.
  -- First, rewrite `(chart.symm z)` as `circleParameter x r θ` to use the
  -- chart-anchored evaluation.
  show logDiffCoeffAt f x ((chartAt ℂ x).symm z)
        = kC * ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))⁻¹
            + deriv g z / g z
  have hcp : (chartAt ℂ x).symm z = circleParameter (X := X) x r θ := by
    unfold circleParameter
    rfl
  rw [hcp, logDiffCoeffAt_circleParameter f x r θ hz_target,
      h_f_eq, h_F_at_z, h_deriv_eq]
  have hZB := logDeriv_zpow_smul_pointwise k z₀ g hz_ne hg_diff_z hgz_ne
  rw [hZB, hz_sub, div_eq_mul_inv]

/-- **Headline ZZ10 deliverable.**

Under per-point regular chart-disk hypotheses, the chart-circle sum
equals the sum of integer orders.

```
chartCircleSum f S r =
  ∑ x ∈ S, ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ).
```

The proof composes the per-point identity
`chartCircleIntegralAnchored_eq_order_of_isRegularChartDiskAround` over
the finite set `S`. -/
theorem chartCircleSum_eq_sum_orders
    (f : MeromorphicNonzero X)
    (S : Finset X) (r : X → ℝ)
    (hreg : ∀ x ∈ S, IsRegularChartDiskAround f x (r x))
    (hr_pos : ∀ x ∈ S, 0 < r x) :
    chartCircleSum f S r =
      ∑ x ∈ S,
        ((MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x : ℤ) : ℂ) := by
  unfold chartCircleSum
  refine Finset.sum_congr rfl (fun x hx => ?_)
  exact chartCircleIntegralAnchored_eq_order_of_isRegularChartDiskAround
    f x (r x) (hr_pos x hx) (hreg x hx)

end MeromorphicNonzero

end JacobianChallenge

end
