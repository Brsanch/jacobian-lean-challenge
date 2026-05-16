/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalFormInverse

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `ψ z ≠ 0` for `z ≠ x₀` near `x₀` (local injectivity of the Hurwitz biholomorphism)

From the eventual left inverse `φ (ψ z) = z` near `x₀`, the Hurwitz
biholomorphism `ψ` is locally injective at `x₀`. Combined with
`ψ x₀ = 0`, this gives: on a punctured neighbourhood of `x₀`, `ψ z ≠ 0`.

This is the missing ingredient for the **divided form** of the
cyclic-sum descent: at `z ≠ x₀` near `x₀`,
`(ψ z)^(k-1) ≠ 0`, so dividing the source-side z-form identity by
`(↑k) · (ψ z)^(k-1)` gives the cleaner chart-coefficient form
`cyclicSum (h ∘ φ) ω k (ψ z) / ((↑k) · (ψ z)^(k-1)) = Q (g z - w₀) / ↑k`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Local non-vanishing of the Hurwitz biholomorphism away from `x₀`.**

If `ψ` is analytic at `x₀` with `ψ x₀ = 0` and admits a continuous local
left inverse `φ` (so `∀ᶠ z in 𝓝 x₀, φ (ψ z) = z`), then `ψ z ≠ 0` for
all `z ≠ x₀` in a neighbourhood of `x₀`. -/
theorem hurwitz_ne_zero_of_ne_x₀
    {ψ φ : ℂ → ℂ} {x₀ : ℂ}
    (hψ_x₀ : ψ x₀ = 0)
    (h_left : ∀ᶠ z in 𝓝 x₀, φ (ψ z) = z) :
    ∀ᶠ z in 𝓝 x₀, z ≠ x₀ → ψ z ≠ 0 := by
  -- Pull back the `φ x₀ = ?` value via `ψ x₀ = 0` and `h_left` at `x₀`.
  -- Strategy: if `ψ z = 0` and `z` near `x₀` satisfies `φ (ψ z) = z`, then
  -- `z = φ 0 = φ (ψ x₀) = x₀` (the last equation needs `x₀` in the
  -- eventual set; trivially `x₀ ∈ 𝓝 x₀`).
  -- So `ψ z = 0 → z = x₀`, i.e. `z ≠ x₀ → ψ z ≠ 0`.
  -- Extract `φ (ψ x₀) = x₀` from `h_left` specialised at `x₀`.
  -- `h_left` is `∀ᶠ z in 𝓝 x₀, ...`, which gives a property at `x₀` via
  -- `Filter.eventually_iff_exists_mem`.
  have h_at_x₀ : φ (ψ x₀) = x₀ := h_left.self_of_nhds
  -- Conclusion via contraposition.
  filter_upwards [h_left] with z hz hne hψ_zero
  -- `ψ z = 0 = ψ x₀`, so `φ (ψ z) = φ 0 = φ (ψ x₀) = x₀`.
  have : z = x₀ := by
    rw [← hz, hψ_zero, ← hψ_x₀]
    exact h_at_x₀
  exact hne this

end Manifold
end JacobianChallenge
