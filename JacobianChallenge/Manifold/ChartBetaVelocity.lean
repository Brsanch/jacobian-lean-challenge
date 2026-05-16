/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Chart-coordinate velocity of a smooth map `β : ℝ → M` anchored at `s₀`

For a smooth map `β : ℝ → M` (where `M` is a manifold modeled on `E`),
define a chart-coordinate representative of the velocity `β'(s) :=
mfderiv β s 1` anchored at the chart `chartAt H (β s₀)` for a fixed
`s₀ : ℝ`. Smoothness at `s₀` follows from `ContMDiffAt.mfderiv_const`.

This is the direct-smooth-map analogue of
`SmoothPath.chartVelocity` (defined in
`SmoothPathIntegrability.lean`), useful for the
chart-coord-pair architecture of `IntegrandContinuousAlongBeta`
where `β : ℝ → RiemannSphere` is given as a smooth map (not
pre-packaged as a `SmoothPath`).

## What ships

* `chartBetaVelocity I β s₀ s` — chart-coord velocity at `s` of `β`
  anchored at chart `chartAt H (β s₀)`, applied to source-tangent `1`.

* `contMDiffAt_chartBetaVelocity` — `ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞`
  at `s₀`.

* `continuousAt_chartBetaVelocity` — `ContinuousAt` corollary.

The `self`-evaluation lemma (`chartBetaVelocity β s₀ s₀ = β'(s₀)`) is
deferred to a follow-up chip: it follows from `inTangentCoordinates_eq`
specialised at `s = s₀` (so `coordChange` collapses to the identity),
mirroring `SmoothPath.integrand_eq_chart_pairing`'s same-point analysis.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

namespace JacobianChallenge

/-- **Chart-coord velocity of `β` anchored at chart `chartAt H (β s₀)`.**

For `β : ℝ → M` smooth and a base parameter `s₀ : ℝ`, this is the
chart-trivialised representative of `mfderiv β s` evaluated at the
source tangent vector `1 : ℝ`. It lives in the model space `E`. -/
def chartBetaVelocity (β : ℝ → M) (s₀ s : ℝ) : E :=
  (inTangentCoordinates 𝓘(ℝ, ℝ) I id β
      (fun s => mfderiv 𝓘(ℝ, ℝ) I β s) s₀ s) (1 : ℝ)

variable {I}

/-- **`chartBetaVelocity` is `ContMDiffAt ∞` at the base parameter.**

This is the source-side `mfderiv_const` machinery from
`Mathlib.Geometry.Manifold.ContMDiffMFDeriv`, applied to a smooth
`β` at `s₀` and post-composed with evaluation at `(1 : ℝ)`. -/
theorem contMDiffAt_chartBetaVelocity
    {β : ℝ → M} (hβ : ContMDiff 𝓘(ℝ, ℝ) I ∞ β) (s₀ : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (chartBetaVelocity I β s₀) s₀ := by
  have h_inT :
      ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ →L[ℝ] E) ∞
        (inTangentCoordinates 𝓘(ℝ, ℝ) I id β
          (fun s => mfderiv 𝓘(ℝ, ℝ) I β s) s₀) s₀ := by
    have h_β_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ β s₀ := hβ s₀
    have h_top : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    exact h_β_at.mfderiv_const h_top
  exact h_inT.clm_apply contMDiffAt_const

/-- **`chartBetaVelocity` is `ContinuousAt` at the base parameter.** -/
theorem continuousAt_chartBetaVelocity
    {β : ℝ → M} (hβ : ContMDiff 𝓘(ℝ, ℝ) I ∞ β) (s₀ : ℝ) :
    ContinuousAt (chartBetaVelocity I β s₀) s₀ :=
  (contMDiffAt_chartBetaVelocity hβ s₀).continuousAt

end JacobianChallenge

end
