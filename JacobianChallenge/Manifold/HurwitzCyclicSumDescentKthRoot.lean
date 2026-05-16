/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCyclicSumDescent
import JacobianChallenge.Manifold.CyclicSumFactorKthPowerDescentKthRoot

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Target-side k-th root form of the Hurwitz + cyclic-sum descent

Composes `hurwitz_cyclic_sum_descent` (chip 3c-3) with
`cyclicSum_factor_descends_kthRoot_form` (chip 3b-5) to re-quantify
the cyclic-sum identity over the target variable `v = ξ^k`.

For `g, h : ℂ → ℂ` analytic at `x₀`, `analyticOrderAt (g - w₀) x₀ = k`
(`k ≥ 2`), primitive k-th root `ω`, there exist `ψ, φ, Q` with the
Hurwitz form, the analytic inverse, and the eventual identity in `v`:

  `∀ᶠ v in 𝓝 0, ∀ ξ : ℂ, ξ^k = v →`
  `    cyclicSum (h ∘ φ) ω k ξ = ξ^(k-1) * Q v`.

This is the form a target-chart-coefficient bridge consumes: the trace
of `α` at a regular value `v = g(z) - w₀ = (ψ z)^k` (with `z = φ(ξ)` for
ξ a k-th root of `v`) is expressed via `Q v` independently of which
k-th root is chosen, because the LHS `cyclicSum / (k · ξ^{k-1})` is
itself manifestly a function of `v` (`= Q(v) / k`).

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Hurwitz + cyclic-sum descent, target-side form.**

Re-quantification of `hurwitz_cyclic_sum_descent` over the target
variable `v = ξ^k`. The descent function `Q` does not depend on the
choice of k-th root of `v`. -/
theorem hurwitz_cyclic_sum_descent_kthRoot_form
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
      (∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s) ∧
      (∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) ∧
      AnalyticAt ℂ Q 0 ∧
      (∀ᶠ v in 𝓝 (0 : ℂ), ∀ ξ : ℂ, ξ ^ k = v →
        JacobianChallenge.cyclicSum (h ∘ φ) ω k ξ = ξ ^ (k - 1) * Q v) := by
  -- Step 1. Apply chip 3c-3 to get ξ-form descent.
  obtain ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          h_right, h_left, Q_an, hQ_eq_ξ⟩ :=
    hurwitz_cyclic_sum_descent hk hg h_w₀ hord h_an hω
  -- Step 2. Re-quantify over v via the k-th-root re-quantification
  -- (chip 3b-5 logic applied directly to the eventual identity).
  have h_comp_an : AnalyticAt ℂ (h ∘ φ) 0 := by
    have hh_at : AnalyticAt ℂ h (φ 0) := by rw [hφ_0]; exact h_an
    exact hh_at.comp hφ_an
  -- Use chip 3b-5's re-quantification: the abstract version
  -- `cyclicSum_factor_descends_kthRoot_form` would re-derive `Q`, but
  -- we want to keep the SAME `Q` as in chip 3c-3. So we re-do the
  -- target-side packaging by hand, using the openness of ξ ↦ ξ^k at 0.
  rcases (Filter.eventually_iff_exists_mem.mp hQ_eq_ξ) with ⟨U, hU_nhds, hU_holds⟩
  have hk_pos : 1 ≤ k := by omega
  have h_pow_event : ∀ᶠ v in 𝓝 (0 : ℂ), ∀ ξ : ℂ, ξ ^ k = v → ξ ∈ U :=
    JacobianChallenge.eventually_forall_pow_kth_root_mem_of_mem_nhds hk_pos hU_nhds
  have h_v_form : ∀ᶠ v in 𝓝 (0 : ℂ), ∀ ξ : ℂ, ξ ^ k = v →
      JacobianChallenge.cyclicSum (h ∘ φ) ω k ξ = ξ ^ (k - 1) * Q v := by
    filter_upwards [h_pow_event] with v hv ξ hξ_pow
    have h_src := hU_holds ξ (hv ξ hξ_pow)
    rw [hξ_pow] at h_src
    exact h_src
  -- Package.
  exact ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
         h_right, h_left, Q_an, h_v_form⟩

end Manifold
end JacobianChallenge
