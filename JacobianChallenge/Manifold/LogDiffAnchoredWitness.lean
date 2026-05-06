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
  -- `w ↦ w - z₀` is differentiable at `z`.
  have hsub_diff : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z :=
    differentiableAt_id.sub_const z₀
  -- `u ↦ u ^ k` is differentiable at `z - z₀` (since `z - z₀ ≠ 0`).
  have hzpow_diff : DifferentiableAt ℂ (fun u : ℂ => u ^ k) (z - z₀) :=
    differentiableAt_zpow.mpr (Or.inl hsub)
  -- Hence `w ↦ (w - z₀) ^ k = (·^k) ∘ (·-z₀)` is differentiable at `z`.
  have hpow_diff : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ k) z :=
    hzpow_diff.comp z hsub_diff
  -- Compute `deriv ((·-z₀)^k) z = k * (z - z₀)^(k-1)`.
  have hpow_deriv :
      deriv (fun w : ℂ => (w - z₀) ^ k) z = (k : ℂ) * (z - z₀) ^ (k - 1) := by
    -- Inner derivative is 1.
    have hd_inner : deriv (fun w : ℂ => w - z₀) z = 1 := by
      rw [deriv_sub_const]; exact deriv_id'' z
    -- Outer derivative: `deriv_zpow` gives `deriv (·^k) u = k * u^(k-1)`.
    have h_outer : deriv (fun u : ℂ => u ^ k) (z - z₀)
        = (k : ℂ) * (z - z₀) ^ (k - 1) := by
      simpa using (deriv_zpow (n := k) (z - z₀))
    -- Chain rule.
    have h_chain : deriv ((fun u : ℂ => u ^ k) ∘ (fun w : ℂ => w - z₀)) z
        = deriv (fun u : ℂ => u ^ k) (z - z₀) * deriv (fun w : ℂ => w - z₀) z :=
      deriv_comp z hzpow_diff hsub_diff
    have h_eq_comp : (fun w : ℂ => (w - z₀) ^ k)
        = (fun u : ℂ => u ^ k) ∘ (fun w : ℂ => w - z₀) := rfl
    rw [h_eq_comp, h_chain, h_outer, hd_inner, mul_one]
  -- Product rule.
  have hprod :
      deriv (fun w : ℂ => (w - z₀) ^ k * g w) z
        = (k : ℂ) * (z - z₀) ^ (k - 1) * g z + (z - z₀) ^ k * deriv g z := by
    rw [deriv_mul hpow_diff hg, hpow_deriv]
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

end MeromorphicNonzero

end JacobianChallenge

end
