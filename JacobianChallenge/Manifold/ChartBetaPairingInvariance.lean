/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartBetaVelocity
import JacobianChallenge.Manifold.SmoothPathIntegral
import JacobianChallenge.Manifold.Cotangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Chart invariance of the cotangent–velocity pairing along `β`

For a smooth map `β : ℝ → M`, an anchor parameter `s₀ : ℝ`, and any
parameter `s` with `β s` in the source of `chartAt H (β s₀)`, the pairing
`applyCotangent φ (mfderiv β s 1)` (for an arbitrary cotangent
`φ : CotangentSpace I (β s)`) admits a chart-coord representation
anchored at the chart of `β s₀`:

```
applyCotangent φ (mfderiv β s 1)
  = ((cotangentBundleCore I M).coordChange i j (β s) φ) (chartBetaVelocity I β s₀ s)
```

where `i = achart H (β s)`, `j = achart H (β s₀)`. The identity is the
cotangent–tangent cocycle cancellation
`coordChange j i x ∘ coordChange i j x = id` at `x = β s`.

Mirrors `SmoothPath.integrand_eq_chart_pairing` but is stated for a
*free* cotangent vector `φ` at `β s` (not pre-packaged as
`ω (β s)` for some `SmoothOneForm`). This decouples the chart-coord
pairing identity from the smoothness of the form-side
(`fStarOmega`/`traceAt`), which is the f-5 blocker.

## What ships

* `applyCotangent_eq_chart_pairing_beta I β s₀ hs φ` — the chart
  invariance identity above.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

namespace JacobianChallenge

variable {I}

/-- **Chart invariance of the cotangent–velocity pairing along `β`.**

On the source of the chart at `β s₀`, the pairing
`applyCotangent φ (mfderiv β s 1)` (for an arbitrary cotangent
`φ : CotangentSpace I (β s)`) equals the chart-coord pairing of `φ`
(transported to the chart at `β s₀`) with `chartBetaVelocity I β s₀ s`.
The cancellation is the tangent-bundle cocycle
`coordChange j i x ∘ coordChange i j x = id` at `x = β s`. -/
theorem applyCotangent_eq_chart_pairing_beta
    (β : ℝ → M) (s₀ : ℝ) {s : ℝ}
    (hs : β s ∈ (chartAt H (β s₀)).source)
    (φ : CotangentSpace I (β s)) :
    SmoothPath.applyCotangent φ ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ))
      = ((cotangentBundleCore I M).coordChange
            (achart H (β s)) (achart H (β s₀)) (β s) φ)
        (chartBetaVelocity I β s₀ s) := by
  -- Chart-source memberships (i = achart at β s, j = achart at β s₀).
  have hi : β s ∈ (achart H (β s)).1.source := mem_chart_source H (β s)
  have hj : β s ∈ (achart H (β s₀)).1.source := hs
  -- Source chart membership on `ℝ` (the model space chart at `s₀`).
  have h_src_chart : (id s) ∈ (chartAt ℝ ((id : ℝ → ℝ) s₀)).source := by
    change s ∈ (chartAt ℝ s₀).source
    simp [chartAt]
  -- Unfold `inTangentCoordinates` via `inTangentCoordinates_eq` at `(s₀, s)`.
  have h_eq_inT :
      inTangentCoordinates 𝓘(ℝ, ℝ) I id β
          (fun u => mfderiv 𝓘(ℝ, ℝ) I β u) s₀ s
        = (tangentBundleCore I M).coordChange
            (achart H (β s)) (achart H (β s₀)) (β s) ∘L
          (mfderiv 𝓘(ℝ, ℝ) I β s) ∘L
          (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange
            (achart ℝ s₀) (achart ℝ s) s :=
    inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := id) (g := β)
      (ϕ := fun u => mfderiv 𝓘(ℝ, ℝ) I β u) h_src_chart hs
  -- Source-side coord change is the identity (model space on `ℝ`).
  have h_src_id :
      (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange (achart ℝ s₀) (achart ℝ s) s
        = ContinuousLinearMap.id ℝ ℝ :=
    tangentBundleCore_coordChange_model_space (I := 𝓘(ℝ, ℝ)) s₀ s s
  -- Repackage `chartBetaVelocity` as a single coord-change application.
  have h_chartVel :
      chartBetaVelocity I β s₀ s
        = (tangentBundleCore I M).coordChange
            (achart H (β s)) (achart H (β s₀)) (β s)
            ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ)) := by
    unfold chartBetaVelocity
    rw [h_eq_inT, h_src_id]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rfl
  -- Unfold the cotangent coord change as right-composition with the
  -- tangent coord change in the opposite direction. `CotangentSpace I x`
  -- is definitionally `E →L[ℝ] ℝ` (the cotangent-bundle-core fiber model),
  -- so `φ` plugs directly into `cotangentBundleCore_coordChange_apply`.
  have h_cot_coord :
      (cotangentBundleCore I M).coordChange
          (achart H (β s)) (achart H (β s₀)) (β s) φ
        = φ.comp ((tangentBundleCore I M).coordChange
            (achart H (β s₀)) (achart H (β s)) (β s)) :=
    cotangentBundleCore_coordChange_apply (I := I)
      (achart H (β s)) (achart H (β s₀)) (β s) φ
  -- Cocycle cancellation at `x = β s`:
  -- `coordChange j i x (coordChange i j x v) = v`, where i ∋ x and j ∋ x.
  have h_cocycle :
      ∀ v : E,
        (tangentBundleCore I M).coordChange
            (achart H (β s₀)) (achart H (β s)) (β s)
            ((tangentBundleCore I M).coordChange
              (achart H (β s)) (achart H (β s₀)) (β s) v)
          = v := by
    intro v
    have h_mem : β s ∈ (tangentBundleCore I M).baseSet (achart H (β s)) ∩
        (tangentBundleCore I M).baseSet (achart H (β s₀)) ∩
        (tangentBundleCore I M).baseSet (achart H (β s)) :=
      ⟨⟨hi, hj⟩, hi⟩
    have h_comp :=
      (tangentBundleCore I M).coordChange_comp
        (achart H (β s)) (achart H (β s₀)) (achart H (β s)) (β s) h_mem v
    rw [h_comp]
    exact (tangentBundleCore I M).coordChange_self (achart H (β s)) (β s) hi v
  -- Assemble.
  rw [h_chartVel, h_cot_coord, ContinuousLinearMap.comp_apply,
    h_cocycle ((mfderiv 𝓘(ℝ, ℝ) I β s) (1 : ℝ))]
  unfold SmoothPath.applyCotangent
  rfl

end JacobianChallenge

end
