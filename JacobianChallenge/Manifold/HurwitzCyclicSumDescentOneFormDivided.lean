/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzCyclicSumDescentOneForm
import JacobianChallenge.Manifold.HurwitzZetaLocalNonzero
import JacobianChallenge.Manifold.CyclicSumFactorKthPowerDescentKthRoot

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # 1-form-corrected divided form of the source-side descent

Headline:

For analytic `g, h : ℂ → ℂ` at `x₀` with `analyticOrderAt (g - w₀) x₀ = k`
(`k ≥ 2`) and primitive `k`-th root `ω`, there exist Hurwitz `ψ, φ` and
analytic `Q : ℂ → ℂ` at `0` such that for `z` near `x₀`, `z ≠ x₀`,

  `cyclicSum ((h / deriv ψ) ∘ φ) ω k (ψ z) / ((↑k) · (ψ z)^(k-1))`
   `= Q (g z - w₀) / ↑k`.

The LHS, by the source-fibre identification + cotangent pullback
formula (downstream chip), equals the chart-coefficient of the trace
1-form `f_*α` at the regular value `(chartAt … v₀).symm (g z)`. The
RHS is the analytic extension across the critical value `w₀ = g x₀`.

This is the **clean chart-coefficient identification** that the bundle
wiring chips will consume to construct the extended trace 1-form on
`RiemannSphere`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **1-form-corrected divided form.** Combines the 1-form descent
(chip 3d-2) with local non-vanishing (chip 3c-6) and the kth-root form
(for the eventual left-inverse) to give the chart-coefficient
identification near a critical value. -/
theorem hurwitz_cyclic_sum_descent_oneForm_divided
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
      (∀ᶠ z in 𝓝 x₀, z ≠ x₀ →
        JacobianChallenge.cyclicSum
            ((fun z => h z / deriv ψ z) ∘ φ) ω k (ψ z)
              / ((k : ℂ) * (ψ z) ^ (k - 1))
          = Q (g z - w₀) / (k : ℂ)) := by
  -- Step 1. Get the 1-form-corrected descent (chip 3d-2).
  obtain ⟨R, ψ, φ, Q, hR_pos, hψ_an, hψ_x₀, hψ'_ne, h_fact, hφ_an, hφ_0,
          Q_an, hQ_eq_ξ⟩ :=
    hurwitz_cyclic_sum_descent_oneForm hk hg h_w₀ hord h_an hω
  -- We need `h_left : ∀ᶠ z in 𝓝 x₀, φ (ψ z) = z` for chip 3c-6.
  -- Re-derive via the inverse function theorem, using the same φ as in
  -- chip 3d-2 (which came from `hurwitz_local_form_with_inverse`).
  have hψ_at_x₀ : AnalyticAt ℂ ψ x₀ :=
    hψ_an x₀ (Metric.mem_closedBall_self hR_pos.le)
  -- The φ in `hurwitz_local_form_with_inverse` is
  -- `hψ_at_x₀.hasStrictDerivAt.localInverse ψ (deriv ψ x₀) x₀ hψ'_ne`.
  -- BUT chip 3d-2 returns an existentially-bound φ; we can't assume it
  -- equals this canonical form. So we extract the eventual left-inverse
  -- via the same construction route, without depending on φ's
  -- definitional shape: use `_h_left` from `hurwitz_local_form_with_inverse`
  -- directly. Rebuild the chip path.
  -- Cleaner: re-extract via the kth-root form (which exposes `h_left`).
  -- But chip 3d-2's Q differs from chip 3c-4's Q (different cyclicSum
  -- input). So we cannot just swap.
  -- Instead: prove `h_left` by going through the inverse function theorem
  -- direct. The φ from chip 3d-2 IS the same canonical localInverse
  -- because `hurwitz_local_form_with_inverse` *defines* it that way.
  -- The existential pack just hides the canonical shape — but we don't
  -- need to reveal it; we just need the eventual identity.
  -- WORKAROUND: re-run `hurwitz_local_form_with_inverse` to grab the
  -- left-inverse property. The φ may not match the chip 3d-2 φ
  -- definitionally, but `Subsingleton`-style uniqueness on a punctured
  -- neighbourhood gives `h_left` for chip 3d-2's φ too.
  -- Actually simplest: re-derive the eventual left-inverse from
  -- `HasStrictDerivAt.eventually_left_inverse`. For chip 3d-2's φ, we
  -- don't have this lemma directly. So we abandon this route.
  --
  -- Real fix: just re-extract `h_left` from `hurwitz_local_form_with_inverse`
  -- and *use that φ* (which is what chip 3d-2's φ also is, definitionally).
  -- We replay chip 3d-2's construction manually so we keep φ visible.
  have hk_pos : 1 ≤ k := by omega
  obtain ⟨R', ψ', φ', hR'_pos, hψ'_an, hψ'_x₀, hψ''_ne, h_fact', hφ'_an,
          hφ'_0, _h_right', h_left'⟩ :=
    hurwitz_local_form_with_inverse hk_pos hg h_w₀ hord
  -- Now build Q' from chip 3b-4 applied to `(h / deriv ψ') ∘ φ'`.
  have hψ'_at_x₀ : AnalyticAt ℂ ψ' x₀ :=
    hψ'_an x₀ (Metric.mem_closedBall_self hR'_pos.le)
  have h_derivψ'_an : AnalyticAt ℂ (deriv ψ') x₀ := hψ'_at_x₀.deriv
  have h_div_an' : AnalyticAt ℂ (fun z => h z / deriv ψ' z) x₀ :=
    h_an.div h_derivψ'_an hψ''_ne
  have h_comp_an' : AnalyticAt ℂ ((fun z => h z / deriv ψ' z) ∘ φ') 0 := by
    have h_at : AnalyticAt ℂ (fun z => h z / deriv ψ' z) (φ' 0) := by
      rw [hφ'_0]; exact h_div_an'
    exact h_at.comp hφ'_an
  obtain ⟨Q', Q'_an, hQ'_eq⟩ :=
    JacobianChallenge.cyclicSum_factor_descends_to_kth_power
      (h := (fun z => h z / deriv ψ' z) ∘ φ') hω hk h_comp_an'
  -- Now we use ψ', φ', Q' (not the chip-3d-2-returned ones; same values
  -- but with the extra `h_left'` accessible).
  refine ⟨R', ψ', φ', Q', hR'_pos, hψ'_an, hψ'_x₀, hψ''_ne, h_fact', hφ'_an,
          hφ'_0, Q'_an, ?_⟩
  -- Derive the z-form via `Tendsto.eventually` on ξ := ψ' z.
  have hψ'_cont : ContinuousAt ψ' x₀ := hψ'_at_x₀.continuousAt
  have hψ'_tendsto : Tendsto ψ' (𝓝 x₀) (𝓝 0) := by
    have h_to_ψ'x₀ : Tendsto ψ' (𝓝 x₀) (𝓝 (ψ' x₀)) := hψ'_cont.tendsto
    simpa [hψ'_x₀] using h_to_ψ'x₀
  have h_z_form : ∀ᶠ z in 𝓝 x₀,
      JacobianChallenge.cyclicSum
          ((fun z => h z / deriv ψ' z) ∘ φ') ω k (ψ' z)
        = (ψ' z) ^ (k - 1) * Q' ((ψ' z) ^ k) :=
    hψ'_tendsto.eventually hQ'_eq
  have h_eq_event : ∀ᶠ z in 𝓝 x₀, g z - w₀ = (ψ' z) ^ k := by
    have hball_nhds : Metric.closedBall x₀ R' ∈ 𝓝 x₀ :=
      Metric.closedBall_mem_nhds x₀ hR'_pos
    filter_upwards [hball_nhds] with z hz
    exact h_fact' z hz
  have h_nz : ∀ᶠ z in 𝓝 x₀, z ≠ x₀ → ψ' z ≠ 0 :=
    hurwitz_ne_zero_of_ne_x₀ hψ'_x₀ h_left'
  have hk_ne_ℂ : (k : ℂ) ≠ 0 := by
    have hk_ne : k ≠ 0 := by omega
    exact_mod_cast hk_ne
  filter_upwards [h_z_form, h_eq_event, h_nz] with z h_eq h_g_eq h_imp hne
  have hψ'z_ne : ψ' z ≠ 0 := h_imp hne
  have hpow_ne : (ψ' z) ^ (k - 1) ≠ 0 := pow_ne_zero _ hψ'z_ne
  have h_denom_ne : (k : ℂ) * (ψ' z) ^ (k - 1) ≠ 0 := mul_ne_zero hk_ne_ℂ hpow_ne
  rw [h_eq, ← h_g_eq]
  field_simp

end Manifold
end JacobianChallenge
