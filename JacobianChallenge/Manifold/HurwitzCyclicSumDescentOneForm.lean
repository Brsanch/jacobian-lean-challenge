/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalFormInverse
import JacobianChallenge.Manifold.CyclicSumFactorKthPowerDescent
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # 1-form-corrected Hurwitz cyclic-sum descent

`HurwitzCyclicSumDescent.lean` (chip 3c-3) uses `h ∘ φ` as the cyclic-
sum input: this is correct as a *function* pullback under the local
biholomorphism `φ = ψ⁻¹`, but it omits the **Jacobian factor** that
arises when pulling back a *1-form*. For the trace-1-form bridge, the
right input is

  `H(s) := h(φ(s)) · φ'(s) = h(φ(s)) / ψ'(φ(s)) = (h / ψ') ∘ φ (s)`,

where `h` is the chart-coefficient of α in the source chart and ψ is
the Hurwitz biholomorphism with non-zero derivative at `x₀`.

Then `cyclicSum H ω k ξ / (k · ξ^(k-1))` equals the chart-coefficient
of the trace 1-form `f_*α` at the target value `v = ξ^k`. By descent,
this is `Q(v) / k` for `Q` analytic at `0`.

This file ships the manifold-style headline:

* `hurwitz_cyclic_sum_descent_oneForm` — given analytic `g, h` at `x₀`
  with order `k ≥ 2` and primitive root `ω`, produces ψ, φ, Q with
  `cyclicSum (λ s, h(φ s) · derivφ s) ω k ξ = ξ^(k-1) · Q(ξ^k)`
  eventually.

The input `(h / ψ') ∘ φ` is analytic at `0` (and equals
`λ s, h(φ s) · φ'(s)` since `φ'(s) = 1/ψ'(φ(s))` at the inverse-image
points), so the pure descent applies directly.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **1-form-corrected Hurwitz cyclic-sum descent.**

For analytic `g, h : ℂ → ℂ` at `x₀` with `analyticOrderAt (g - w₀) x₀ = k`
(`k ≥ 2`), primitive `k`-th root `ω`, produces Hurwitz `ψ, φ` and
analytic `Q : ℂ → ℂ` at `0` with

  `cyclicSum ((h / deriv ψ) ∘ φ) ω k ξ = ξ ^ (k - 1) * Q (ξ ^ k)`

eventually in ξ near `0`. The input `(h / deriv ψ) ∘ φ` is the
**1-form chart-coefficient transform** of `h` under the Hurwitz
biholomorphism `ψ`, matching the trace-1-form bridge identity. -/
theorem hurwitz_cyclic_sum_descent_oneForm
    {g h : ℂ → ℂ} {x₀ w₀ ω : ℂ} {k : ℕ}
    (hk : 2 ≤ k)
    (hg : AnalyticAt ℂ g x₀)
    (h_w₀ : g x₀ = w₀)
    (hord : analyticOrderAt (fun z => g z - w₀) x₀ = (k : ℕ∞))
    (h_an : AnalyticAt ℂ h x₀)
    (hω : IsPrimitiveRoot ω k) :
    ∃ (R : ℝ) (ψ : ℂ → ℂ) (φ : ℂ → ℂ) (Q : ℂ → ℂ),
      0 < R ∧
      AnalyticOnNhd ℂ ψ (Metric.closedBall x₀ R) ∧
      ψ x₀ = 0 ∧ deriv ψ x₀ ≠ 0 ∧
      (∀ z ∈ Metric.closedBall x₀ R, g z - w₀ = (ψ z) ^ k) ∧
      AnalyticAt ℂ φ 0 ∧
      φ 0 = x₀ ∧
      AnalyticAt ℂ Q 0 ∧
      (∀ᶠ ξ in 𝓝 (0 : ℂ),
        JacobianChallenge.cyclicSum ((fun z => h z / deriv ψ z) ∘ φ) ω k ξ
          = ξ ^ (k - 1) * Q (ξ ^ k)) := by
  have hk_pos : 1 ≤ k := by omega
  -- Step 1. Hurwitz local form with inverse.
  obtain ⟨R, ψ, φ, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          _h_right, _h_left⟩ :=
    hurwitz_local_form_with_inverse hk_pos hg h_w₀ hord
  have hψ_at_x₀ : AnalyticAt ℂ ψ x₀ :=
    hψ_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  -- Step 2. `deriv ψ` is analytic at `x₀` and non-zero there.
  have h_derivψ_an : AnalyticAt ℂ (deriv ψ) x₀ := hψ_at_x₀.deriv
  -- Step 3. `h / deriv ψ` is analytic at `x₀`.
  have h_div_an : AnalyticAt ℂ (fun z => h z / deriv ψ z) x₀ :=
    h_an.div h_derivψ_an hψ'_ne
  -- Step 4. `(h / deriv ψ) ∘ φ` is analytic at `0` (using `φ 0 = x₀`).
  have h_comp_an : AnalyticAt ℂ ((fun z => h z / deriv ψ z) ∘ φ) 0 := by
    have h_at : AnalyticAt ℂ (fun z => h z / deriv ψ z) (φ 0) := by
      rw [hφ_0]; exact h_div_an
    exact h_at.comp hφ_an
  -- Step 5. Apply pure descent.
  obtain ⟨Q, Q_an, hQ_eq⟩ :=
    JacobianChallenge.cyclicSum_factor_descends_to_kth_power
      (h := (fun z => h z / deriv ψ z) ∘ φ) hω hk h_comp_an
  exact ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
         Q_an, hQ_eq⟩

end Manifold
end JacobianChallenge
