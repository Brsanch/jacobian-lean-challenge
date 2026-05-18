/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartContainedLoopBridgeFromPointwise
import JacobianChallenge.Manifold.SmoothPathIntegrability

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Continuity of the ℂ-valued integrand `t ↦ (α.eval (γ t)) (γ.velocity t)`

The benign continuity hypothesis of
`chartContainedLoopVanishingHypothesis_from_pointwise`.

Decomposes via real/imag parts:
* `Re((α.eval x) v) = γ.integrand (realComponent α) t` (existing).
* `Im((α.eval x) v) = γ.integrand (imagComponent α) t` (existing).

Both real-valued integrands are continuous (`continuous_integrand`).
The ℂ-valued integrand is then `(↑Re + I * ↑Im) : ℝ → ℂ`, continuous
by combination.

## What this file ships

* `complexEvalIntegrand_continuous` — continuity of the ℂ-valued
  integrand on all of `ℝ` for a `SmoothPath` and `HolomorphicOneForm`.
* `complexEvalIntegrand_continuousOn` — restriction to `[0, 1]` (the
  form needed by `chartContainedLoopVanishingHypothesis_from_pointwise`).
* `chartContainedLoopVanishingHypothesis_from_pointwise_only` —
  collapses the chart-contained-loop vanishing to **just**
  `PointwiseChartEvalIdentity` (no `h_cont` hypothesis).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Complex MeasureTheory

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace ChartContainedClosedLoop

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

/-- The ℂ-valued integrand decomposes as
`↑(γ.integrand (realComponent α)) + I * ↑(γ.integrand (imagComponent α))`
pointwise. -/
lemma complexEvalIntegrand_decomp
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) (t : ℝ) :
    (α.eval (γ.ambient t)) (γ.velocity t)
      = ((γ.integrand (realComponent α) t : ℝ) : ℂ)
        + Complex.I * ((γ.integrand (imagComponent α) t : ℝ) : ℂ) := by
  -- Use the existing `integrand_realComponent` / `integrand_imagComponent`
  -- identities to rewrite the real/imag parts of the ℂ-valued pairing.
  -- They live in a section that requires a `ChartContainedClosedLoop`; we
  -- need the bare-form, derived from `applyCotangent_realComponent` etc.
  have h_re : (γ.integrand (realComponent α) t)
      = ((α.eval (γ.ambient t)) (γ.velocity t)).re := by
    unfold SmoothPath.integrand
    exact applyCotangent_realComponent (X := X) α (γ.ambient t) (γ.velocity t)
  have h_im : (γ.integrand (imagComponent α) t)
      = ((α.eval (γ.ambient t)) (γ.velocity t)).im := by
    unfold SmoothPath.integrand
    exact applyCotangent_imagComponent (X := X) α (γ.ambient t) (γ.velocity t)
  rw [h_re, h_im]
  -- `↑z.re + I * ↑z.im = z`, since `↑z.re + ↑z.im * I = z` by `Complex.re_add_im`.
  have h := Complex.re_add_im ((α.eval (γ.ambient t)) (γ.velocity t))
  rw [mul_comm Complex.I _]
  exact h.symm

/-- **Continuity of the ℂ-valued integrand on `ℝ`.** -/
theorem complexEvalIntegrand_continuous
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) :
    Continuous (fun t : ℝ => (α.eval (γ.ambient t)) (γ.velocity t)) := by
  -- The integrand equals `↑(γ.integrand (realComponent α)) + I * ↑(γ.integrand (imagComponent α))`.
  have h_eq : (fun t : ℝ => (α.eval (γ.ambient t)) (γ.velocity t))
      = (fun t : ℝ => ((γ.integrand (realComponent α) t : ℝ) : ℂ)
          + Complex.I * ((γ.integrand (imagComponent α) t : ℝ) : ℂ)) := by
    funext t
    exact complexEvalIntegrand_decomp γ α t
  rw [h_eq]
  -- Continuity of the right-hand side by composition.
  have h_re_cont : Continuous (γ.integrand (realComponent α)) :=
    SmoothPath.continuous_integrand γ (realComponent α)
  have h_im_cont : Continuous (γ.integrand (imagComponent α)) :=
    SmoothPath.continuous_integrand γ (imagComponent α)
  have h_re_C : Continuous (fun t : ℝ => ((γ.integrand (realComponent α) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_re_cont
  have h_im_C : Continuous (fun t : ℝ => ((γ.integrand (imagComponent α) t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h_im_cont
  exact h_re_C.add (continuous_const.mul h_im_C)

/-- **Continuity restricted to `[0, 1]`** — the form used by
`chartContainedLoopVanishingHypothesis_from_pointwise`. -/
theorem complexEvalIntegrand_continuousOn
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) (α : HolomorphicOneForm X) :
    ContinuousOn
      (fun t : ℝ => (α.eval (γ.ambient t)) (γ.velocity t))
      (Set.Icc (0 : ℝ) 1) :=
  (complexEvalIntegrand_continuous γ α).continuousOn

/-- **Collapse to `PointwiseChartEvalIdentity` only.** With the ℂ-integrand
continuity discharged unconditionally, `chartContainedLoopVanishingHypothesis`
needs only the substantive `PointwiseChartEvalIdentity` for every chart-
contained closed loop + form. -/
theorem chartContainedLoopVanishingHypothesis_from_pointwise_only
    (h_point :
      ∀ (data : ChartContainedClosedLoop (X := X)) (α : HolomorphicOneForm X),
        PointwiseChartEvalIdentity data α) :
    ChartContainedLoopVanishingHypothesis (X := X) :=
  chartContainedLoopVanishingHypothesis_from_pointwise h_point
    (fun data α => complexEvalIntegrand_continuousOn data.γ α)

end ChartContainedClosedLoop

end JacobianChallenge

end
