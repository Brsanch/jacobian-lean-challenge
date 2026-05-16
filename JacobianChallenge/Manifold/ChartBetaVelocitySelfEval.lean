/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ChartBetaVelocity
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Same-point self-evaluation of `chartBetaVelocity`

At the anchor parameter `s = s₀`, the chart-coord velocity collapses to the
intrinsic velocity `mfderiv β s₀ 1`. Both the source-side and target-side
tangent-bundle cocycles reduce to the identity by
`tangentBundleCore.coordChange_self`.

Mirrors the same-point analysis in `SmoothPath.integrand_eq_chart_pairing`
specialised at `t = t₀`, but stated as a free identity on a smooth map
`β : ℝ → M` (no `SmoothPath` wrapper).

## What ships

* `chartBetaVelocity_self I β s₀` —
  `chartBetaVelocity I β s₀ s₀ = mfderiv 𝓘(ℝ, ℝ) I β s₀ 1`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]

namespace JacobianChallenge

/-- **Same-point self-evaluation of `chartBetaVelocity`.**

At the anchor parameter `s₀`, both the source-side cocycle (on `ℝ`, model
space) and the target-side cocycle (`coordChange i i` at the chart's own
base point) reduce to the identity. Hence

  `chartBetaVelocity I β s₀ s₀ = mfderiv 𝓘(ℝ, ℝ) I β s₀ 1`. -/
theorem chartBetaVelocity_self (β : ℝ → M) (s₀ : ℝ) :
    chartBetaVelocity I β s₀ s₀ = mfderiv 𝓘(ℝ, ℝ) I β s₀ (1 : ℝ) := by
  -- Chart-source memberships needed by `inTangentCoordinates_eq` at `x = x₀ = s₀`.
  have h_src : (id s₀) ∈ (chartAt ℝ ((id : ℝ → ℝ) s₀)).source := by
    change s₀ ∈ (chartAt ℝ s₀).source
    simp [chartAt]
  have h_tgt : β s₀ ∈ (chartAt H (β s₀)).source := mem_chart_source H (β s₀)
  -- Unfold `inTangentCoordinates` at the diagonal point `(s₀, s₀)`.
  have h_eq :
      inTangentCoordinates 𝓘(ℝ, ℝ) I id β
          (fun s => mfderiv 𝓘(ℝ, ℝ) I β s) s₀ s₀
        = (tangentBundleCore I M).coordChange
            (achart H (β s₀)) (achart H (β s₀)) (β s₀) ∘L
          (mfderiv 𝓘(ℝ, ℝ) I β s₀) ∘L
          (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange
            (achart ℝ s₀) (achart ℝ s₀) s₀ :=
    inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
      (f := id) (g := β)
      (ϕ := fun s => mfderiv 𝓘(ℝ, ℝ) I β s) h_src h_tgt
  -- Source-side cocycle on `ℝ` is the identity (model space).
  have h_src_id :
      (tangentBundleCore 𝓘(ℝ, ℝ) ℝ).coordChange
        (achart ℝ s₀) (achart ℝ s₀) s₀
        = ContinuousLinearMap.id ℝ ℝ :=
    tangentBundleCore_coordChange_model_space (I := 𝓘(ℝ, ℝ)) s₀ s₀ s₀
  -- Target-side cocycle at `i = j = achart H (β s₀)`, base `β s₀`, is the identity.
  have h_tgt_id_v :
      ∀ v : TangentSpace I (β s₀),
        (tangentBundleCore I M).coordChange
          (achart H (β s₀)) (achart H (β s₀)) (β s₀) v = v := fun v =>
    (tangentBundleCore I M).coordChange_self
      (achart H (β s₀)) (β s₀) (mem_chart_source H (β s₀)) v
  -- Combine.
  unfold chartBetaVelocity
  rw [h_eq]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, h_src_id,
    h_tgt_id_v]
  rfl


end JacobianChallenge

end
