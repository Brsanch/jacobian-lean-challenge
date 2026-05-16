/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzLocalFormInverse
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pure-planar fibre-point distinctness via Hurwitz parameterization

For the Hurwitz inverse `φ` with `ψ ∘ φ = id` eventually, and `ζ` a
**primitive** `k`-th root of unity: for non-zero ξ near 0 and
distinct `j₁, j₂ ∈ range k`, the values `φ (ζ^j₁ · ξ)` and
`φ (ζ^j₂ · ξ)` are distinct.

Proof: if `φ (ζ^j₁ · ξ) = φ (ζ^j₂ · ξ)`, apply `ψ` to both sides:
`ψ (φ (ζ^j₁ · ξ)) = ζ^j₁ · ξ` (left-inverse property) and similarly
on the right. Hence `ζ^j₁ · ξ = ζ^j₂ · ξ`, so `(ζ^j₁ - ζ^j₂) · ξ = 0`.
Since ξ ≠ 0, `ζ^j₁ = ζ^j₂`, and since ζ is a primitive `k`-th root,
`j₁ ≡ j₂ (mod k)`, hence `j₁ = j₂` for `j₁, j₂ ∈ range k`.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Planar fibre-point distinctness — eventually form.**

If `ψ (φ s) = s` eventually as `s → 0` and `ζ` is a primitive k-th root
of unity, then for ξ near 0 with ξ ≠ 0 and j₁ ≠ j₂ both `< k`,
`φ(ζ^j₁ · ξ) ≠ φ(ζ^j₂ · ξ)`. -/
theorem hurwitz_fibre_distinct_eventually
    {ψ φ : ℂ → ℂ} {ζ : ℂ} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ k)
    (h_right : ∀ᶠ s in 𝓝 (0 : ℂ), ψ (φ s) = s) :
    ∀ᶠ ξ in 𝓝 (0 : ℂ), ξ ≠ 0 →
      ∀ j₁ j₂ : ℕ, j₁ < k → j₂ < k → j₁ ≠ j₂ →
        φ (ζ ^ j₁ * ξ) ≠ φ (ζ ^ j₂ * ξ) := by
  -- Pull `h_right` back along each ζ^j multiplication. Since we only
  -- have finitely many j ∈ range k, the simultaneous eventual form is
  -- itself eventual.
  have h_mul_tendsto : ∀ j : ℕ,
      Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    intro j
    have : Tendsto (fun ξ : ℂ => ζ ^ j * ξ) (𝓝 0) (𝓝 (ζ ^ j * 0)) :=
      (continuous_const.mul continuous_id).continuousAt.tendsto
    simpa using this
  have h_each : ∀ j : ℕ, ∀ᶠ ξ in 𝓝 (0 : ℂ), ψ (φ (ζ ^ j * ξ)) = ζ ^ j * ξ :=
    fun j => (h_mul_tendsto j).eventually h_right
  -- Collect the eventual statements over `j ∈ range k` using
  -- `Filter.eventually_all_finset`.
  have h_collect : ∀ᶠ ξ in 𝓝 (0 : ℂ),
      ∀ j ∈ Finset.range k, ψ (φ (ζ ^ j * ξ)) = ζ ^ j * ξ := by
    rw [Filter.eventually_all_finset]
    intro j _
    exact h_each j
  filter_upwards [h_collect] with ξ hξ hξ_ne j₁ j₂ hj₁ hj₂ hne hφ_eq
  -- Apply ψ to both sides of `hφ_eq : φ (ζ^j₁ · ξ) = φ (ζ^j₂ · ξ)`.
  have h_psi_eq : ψ (φ (ζ ^ j₁ * ξ)) = ψ (φ (ζ ^ j₂ * ξ)) := by rw [hφ_eq]
  have h_lhs : ψ (φ (ζ ^ j₁ * ξ)) = ζ ^ j₁ * ξ :=
    hξ j₁ (Finset.mem_range.mpr hj₁)
  have h_rhs : ψ (φ (ζ ^ j₂ * ξ)) = ζ ^ j₂ * ξ :=
    hξ j₂ (Finset.mem_range.mpr hj₂)
  rw [h_lhs, h_rhs] at h_psi_eq
  -- `ζ^j₁ · ξ = ζ^j₂ · ξ` and `ξ ≠ 0` give `ζ^j₁ = ζ^j₂`.
  have hζ_pow_eq : ζ ^ j₁ = ζ ^ j₂ := by
    have h_sub : (ζ ^ j₁ - ζ ^ j₂) * ξ = 0 := by linear_combination h_psi_eq
    rcases mul_eq_zero.mp h_sub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hξ_ne
  -- ζ primitive k-th root and j₁, j₂ < k ⇒ j₁ = j₂.
  exact hne (hζ.pow_inj hj₁ hj₂ hζ_pow_eq)

end Manifold
end JacobianChallenge
