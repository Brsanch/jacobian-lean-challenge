/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexManifoldRealification
import JacobianChallenge.Manifold.CotangentBundleSmoothness
import JacobianChallenge.Manifold.HolomorphicOneFormRealification
import JacobianChallenge.Manifold.HolomorphicOneFormRealificationLinearity
import JacobianChallenge.Manifold.SmoothOneForm
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # The real and imaginary components of a holomorphic 1-form as `ℝ`-linear maps

This file packages the fibrewise real-part / imaginary-part operation
`φ ↦ reCLM ∘L (φ.restrictScalars ℝ)` from
`HolomorphicOneFormRealification.lean` as continuous **ℝ**-linear maps

```
realPartCLM, imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ)
```

These bundled CLMs are the load-bearing fibrewise object for the bundled
`SmoothOneForm 𝓘(ℝ, ℂ) X` construction — they let downstream chips compose
the holomorphic section `om.eval` with a continuous **ℝ**-linear fibrewise
map and invoke `ContMDiff.clm_apply` to obtain smoothness of the real/imag
component as a manifold map. The bundle-section wrapping (using
`cotangentSection_contMDiffAt_iff` for both the complex and real cotangent
bundles) is then a separate compositional step.

## Implementation notes

The construction `(compL ℝ ℂ ℂ ℝ reCLM).comp restrictScalarsL` hits the
standard `NormedSpace ℝ ℂ` diamond (between `NormedSpace.complexToReal`
and `NormedAlgebra.toNormedSpace`) inside `restrictScalarsL`'s
`[IsScalarTower 𝕜 𝕜' E]` requirement. Pinning the algebra-based
`NormedSpace ℝ ℂ` per def via `letI` breaks the diamond, just as for
`ComplexManifoldRealification.lean`'s
`contDiffOn_real_chart_trans_of_complex`.

The pointwise apply lemmas relating `realPartCLM φ` to the existing
unbundled `Complex.reCLM.comp (φ.restrictScalars ℝ)` require an explicit
`ext` + `simp` of the underlying composition; `rfl` does not suffice once
the `compL` / `restrictScalarsL` bundles are involved.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

universe u

/-! ## Fibrewise real-part / imaginary-part `ℝ`-linear maps -/

/-- The fibrewise **real-part** operation on the holomorphic cotangent fibre
`(ℂ →L[ℂ] ℂ)`, packaged as a continuous **ℝ**-linear map into the real
cotangent fibre `(ℂ →L[ℝ] ℝ)`.

Concretely: `φ ↦ reCLM ∘L (φ.restrictScalars ℝ)`. This is the bundled
version of the pointwise `HolomorphicOneForm.realPart x` from
`HolomorphicOneFormRealification.lean`. -/
def realPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp
    (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)

/-- The fibrewise **imaginary-part** operation, packaged as a continuous
**ℝ**-linear map. Concretely: `φ ↦ imCLM ∘L (φ.restrictScalars ℝ)`. -/
def imagPartCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  exact (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp
    (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)

theorem realPartCLM_apply (φ : ℂ →L[ℂ] ℂ) :
    realPartCLM φ = Complex.reCLM.comp (φ.restrictScalars ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  show ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.reCLM).comp
          (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)) φ
        = Complex.reCLM.comp (φ.restrictScalars ℝ)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  congr 1

theorem imagPartCLM_apply (φ : ℂ →L[ℂ] ℂ) :
    imagPartCLM φ = Complex.imCLM.comp (φ.restrictScalars ℝ) := by
  letI : NormedSpace ℝ ℂ := @NormedAlgebra.toNormedSpace ℝ ℂ _ _ _
  show ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp
          (ContinuousLinearMap.restrictScalarsL ℂ ℂ ℂ ℝ ℝ)) φ
        = Complex.imCLM.comp (φ.restrictScalars ℝ)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  congr 1

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- The pointwise `realPartCLM` applied to `om.eval x` is exactly the
pointwise `om.realPart x` from `HolomorphicOneFormRealification.lean`. -/
theorem realPartCLM_eval (om : HolomorphicOneForm X) (x : X) :
    realPartCLM (om.eval x) = om.realPart x := by
  rw [realPartCLM_apply]
  rfl

/-- The pointwise `imagPartCLM` applied to `om.eval x` is exactly
`om.imagPart x`. -/
theorem imagPartCLM_eval (om : HolomorphicOneForm X) (x : X) :
    imagPartCLM (om.eval x) = om.imagPart x := by
  rw [imagPartCLM_apply]
  rfl

end JacobianChallenge

end
