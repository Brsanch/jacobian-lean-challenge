/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathIntegral
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Bilinear continuity of `SmoothPath.applyCotangent`

`SmoothPath.applyCotangent` (defined in `SmoothPathIntegral.lean`) is
the pairing

```
applyCotangent : CotangentSpace I x → E → ℝ
applyCotangent φ v := (cotangentEquiv φ) v
```

with `cotangentEquiv : CotangentSpace I x ≃ₗ[ℝ] (E →L[ℝ] ℝ)` an
identity-on-data linear equivalence (it threads the irreducible
`CotangentSpace` type synonym onto the concrete operator space without
re-bundling).

Continuity of the pointwise pairing in a parameter `y : Y` reduces to
the bilinearity of continuous-linear-map evaluation
(`Continuous.clm_apply` / `ContinuousOn.clm_apply` /
`ContinuousAt.clm_apply` / `ContinuousWithinAt.clm_apply` from
`Mathlib.Analysis.Normed.Operator.BoundedLinearMaps`), once the
cotangent factor has been viewed through `cotangentEquiv`.

These primitives are downstream feeders for the discharge of
`MeromorphicNonzero.IntegrandContinuousAlongBeta` (see
`IntegrateLevelSetChainSigmaReparam.lean`): the integrand factors
through `applyCotangent` of `traceAt` against `mfderiv β · 1`, so the
joint continuity statement is exactly the conclusion below.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace SmoothPath

variable {Y : Type*} [TopologicalSpace Y]

/-- **Pointwise `applyCotangent` is continuous on a set** whenever the
cotangent factor (viewed through `cotangentEquiv`) and the vector
factor are each continuous on that set.

The hypothesis on `φ` is stated through `cotangentEquiv` because the
underlying `CotangentSpace` is a non-reducible type synonym; the
mathlib bilinear-application continuity lemma
`ContinuousOn.clm_apply` operates on the concrete operator space
`E →L[ℝ] ℝ`. -/
theorem continuousOn_applyCotangent
    {γ : Y → X} {φ : (y : Y) → CotangentSpace I (γ y)} {v : Y → E}
    {S : Set Y}
    (hφ : ContinuousOn (fun y => (cotangentEquiv (φ y) : E →L[ℝ] ℝ)) S)
    (hv : ContinuousOn v S) :
    ContinuousOn (fun y => applyCotangent (φ y) (v y)) S := by
  unfold applyCotangent
  exact hφ.clm_apply hv

/-- **Pointwise `applyCotangent` is continuous** whenever the cotangent
and vector factors are each continuous. -/
theorem continuous_applyCotangent
    {γ : Y → X} {φ : (y : Y) → CotangentSpace I (γ y)} {v : Y → E}
    (hφ : Continuous (fun y => (cotangentEquiv (φ y) : E →L[ℝ] ℝ)))
    (hv : Continuous v) :
    Continuous (fun y => applyCotangent (φ y) (v y)) := by
  unfold applyCotangent
  exact hφ.clm_apply hv

/-- **Pointwise `applyCotangent` is continuous at a point** whenever
each factor is. -/
theorem continuousAt_applyCotangent
    {γ : Y → X} {φ : (y : Y) → CotangentSpace I (γ y)} {v : Y → E}
    {y₀ : Y}
    (hφ : ContinuousAt (fun y => (cotangentEquiv (φ y) : E →L[ℝ] ℝ)) y₀)
    (hv : ContinuousAt v y₀) :
    ContinuousAt (fun y => applyCotangent (φ y) (v y)) y₀ := by
  unfold applyCotangent
  exact hφ.clm_apply hv

/-- **Pointwise `applyCotangent` is continuous within a set at a point**
whenever each factor is. -/
theorem continuousWithinAt_applyCotangent
    {γ : Y → X} {φ : (y : Y) → CotangentSpace I (γ y)} {v : Y → E}
    {S : Set Y} {y₀ : Y}
    (hφ : ContinuousWithinAt (fun y => (cotangentEquiv (φ y) : E →L[ℝ] ℝ)) S y₀)
    (hv : ContinuousWithinAt v S y₀) :
    ContinuousWithinAt (fun y => applyCotangent (φ y) (v y)) S y₀ := by
  unfold applyCotangent
  exact hφ.clm_apply hv

end SmoothPath

end
