/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.CriticalFibreOneFormDescent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Trace-extension chart coefficient: `Q / k` packaging

Chip 3d-4 produces an analytic `Q : ℂ → ℂ` at `0` such that, for `x`
near the chart image of a critical fibre point `z₀`, `Q (f.chartPullback z₀ x - w₀) / k`
is the **chart-coefficient of the extended trace 1-form** at the chart
image of the target value `v = f z` where `z := (chartAt ℂ z₀).symm x`.

This file packages `traceExtensionChartCoeff Q k v := Q v / ↑k` as an
explicit named function with its analyticity at `0`. Downstream bundle
chips consume this as the chart-coefficient of the extended `f_*α` near
the critical value.

No `sorry`, no `axiom`. -/

namespace JacobianChallenge
namespace Manifold

/-- **Trace-extension chart coefficient.** Given `Q : ℂ → ℂ` from the
1-form-corrected divided form (chip 3d-3/3d-4) and `k : ℕ` (the
ramification index ≥ 2 at a critical fibre point), the analytic
extension of the trace 1-form's chart-coefficient across the critical
value is `v ↦ Q v / ↑k`. -/
noncomputable def traceExtensionChartCoeff (Q : ℂ → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun v => Q v / (k : ℂ)

@[simp] lemma traceExtensionChartCoeff_apply (Q : ℂ → ℂ) (k : ℕ) (v : ℂ) :
    traceExtensionChartCoeff Q k v = Q v / (k : ℂ) := rfl

/-- **Analyticity of the trace-extension chart coefficient at `0`.**
Follows from `AnalyticAt ℂ Q 0` and `(k : ℂ) ≠ 0` (since `k ≥ 1`). -/
theorem traceExtensionChartCoeff_analyticAt
    {Q : ℂ → ℂ} {k : ℕ} (hQ : AnalyticAt ℂ Q 0) (hk : 1 ≤ k) :
    AnalyticAt ℂ (traceExtensionChartCoeff Q k) 0 := by
  have hk_ne_ℂ : (k : ℂ) ≠ 0 := by
    have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk
    exact_mod_cast hk_ne
  -- `Q v / k = Q v · (1 / k)`. Constant multiple of analytic is analytic.
  show AnalyticAt ℂ (fun v => Q v / (k : ℂ)) 0
  have h_const : AnalyticAt ℂ (fun _ : ℂ => (k : ℂ)) 0 := analyticAt_const
  exact hQ.div h_const hk_ne_ℂ

end Manifold
end JacobianChallenge
