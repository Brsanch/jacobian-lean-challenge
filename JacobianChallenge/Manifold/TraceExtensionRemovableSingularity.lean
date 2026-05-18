/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.TraceExtensionChartCoeff
import JacobianChallenge.Manifold.RemovableSingularityAdapter

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Bundle-wiring bridge: `traceExtensionChartCoeff` + removable singularity

The algebraic descent (chip 3d-3, `hurwitz_cyclic_sum_descent_oneForm_divided`)
gives an `AnalyticAt ℂ Q 0` together with the divided-form identity. The
extended trace 1-form's chart-coefficient candidate at a critical value `w₀`
is therefore `fun v => traceExtensionChartCoeff Q k (v - w₀) = Q (v - w₀) / k`,
an `AnalyticAt w₀` function.

This file packages that observation as a *one-shot* removable-singularity
lemma: if a scalar `g : ℂ → ℂ` matches `traceExtensionChartCoeff Q k (· - w₀)`
on a punctured nbhd of `w₀`, then the canonical removable extension of `g`
across `w₀` is `AnalyticAt w₀` — no boundedness hypothesis required.

The downstream consumer is the bundle-wiring chip that identifies the
chart-pulldown of `f.fStarOmegaHol hnc α` near a critical value `v₀` of `f`
with the algebraic descent expression on the *punctured* chart-disc.

No `sorry`, no `axiom`. -/

open Filter Topology

namespace JacobianChallenge
namespace Manifold

/-- **Translate-of-Q is analytic at the shift point.**
For `Q : ℂ → ℂ` analytic at `0`, the function `v ↦ Q (v - w₀)` is analytic
at `w₀`. -/
theorem analyticAt_Q_sub_const
    {Q : ℂ → ℂ} {w₀ : ℂ} (hQ : AnalyticAt ℂ Q 0) :
    AnalyticAt ℂ (fun v : ℂ => Q (v - w₀)) w₀ := by
  have h_shift : AnalyticAt ℂ (fun v : ℂ => v - w₀) w₀ :=
    analyticAt_id.sub analyticAt_const
  have h_shift_val : (fun v : ℂ => v - w₀) w₀ = 0 := by
    show w₀ - w₀ = 0; ring
  exact hQ.comp_of_eq' h_shift h_shift_val

/-- **Translate-of-`traceExtensionChartCoeff Q k` is analytic at the shift.**
The candidate extended chart-coefficient `v ↦ Q (v - w₀) / k` is analytic
at `w₀` for `Q` analytic at `0` and `k ≥ 1`. -/
theorem analyticAt_traceExtensionChartCoeff_sub_const
    {Q : ℂ → ℂ} {w₀ : ℂ} {k : ℕ}
    (hQ : AnalyticAt ℂ Q 0) (hk : 1 ≤ k) :
    AnalyticAt ℂ (fun v : ℂ => traceExtensionChartCoeff Q k (v - w₀)) w₀ := by
  have hQshift : AnalyticAt ℂ (fun v : ℂ => Q (v - w₀)) w₀ :=
    analyticAt_Q_sub_const hQ
  have hk_ne_ℂ : (k : ℂ) ≠ 0 := by
    have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    exact_mod_cast hk_ne
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (k : ℂ)) w₀ := analyticAt_const
  -- `traceExtensionChartCoeff Q k v = Q v / k`, so the shifted version is
  -- `(Q (v - w₀)) / k`.
  show AnalyticAt ℂ (fun v : ℂ => Q (v - w₀) / (k : ℂ)) w₀
  exact hQshift.div hconst hk_ne_ℂ

/-- **Bundle-wiring removable extension via the algebraic descent.**
If a scalar `g : ℂ → ℂ` matches the candidate extended chart-coefficient
`v ↦ Q (v - w₀) / k` on a punctured nbhd of `w₀`, then the canonical
removable extension `removable_extension g w₀` is `AnalyticAt w₀`. -/
theorem removable_extension_analyticAt_of_traceExtensionChartCoeff_eventuallyEq
    {g Q : ℂ → ℂ} {w₀ : ℂ} {k : ℕ}
    (hQ : AnalyticAt ℂ Q 0) (hk : 1 ≤ k)
    (h_eq : g =ᶠ[𝓝[≠] w₀]
              fun v => traceExtensionChartCoeff Q k (v - w₀)) :
    AnalyticAt ℂ (removable_extension g w₀) w₀ :=
  removable_extension_analyticAt_of_analyticAt_eventuallyEq
    (analyticAt_traceExtensionChartCoeff_sub_const hQ hk) h_eq

/-- **Value at `w₀` of the bundle-wiring removable extension.**
Under the same hypotheses, the value at `w₀` is `Q 0 / k`. Useful for
bundle-wiring chips that need to compute the explicit chart-coefficient
of the extended trace 1-form at the critical value itself. -/
theorem removable_extension_value_of_traceExtensionChartCoeff_eventuallyEq
    {g Q : ℂ → ℂ} {w₀ : ℂ} {k : ℕ}
    (hQ : AnalyticAt ℂ Q 0) (hk : 1 ≤ k)
    (h_eq : g =ᶠ[𝓝[≠] w₀]
              fun v => traceExtensionChartCoeff Q k (v - w₀)) :
    removable_extension g w₀ w₀ = Q 0 / (k : ℂ) := by
  have h_val := removable_extension_value_of_analyticAt_eventuallyEq
    (analyticAt_traceExtensionChartCoeff_sub_const hQ hk) h_eq
  -- `h_val : removable_extension g w₀ w₀ = traceExtensionChartCoeff Q k (w₀ - w₀)`
  -- (beta-reduced from the lambda). Now `w₀ - w₀ = 0` and
  -- `traceExtensionChartCoeff Q k 0 = Q 0 / k` (definitional).
  rw [h_val, sub_self]
  rfl

end Manifold
end JacobianChallenge
