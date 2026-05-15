/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminormInner
import JacobianChallenge.Manifold.DiskChartCoverArzela

set_option diagnostics.threshold 100

/-! # `localCoeffMaxInner` ↔ `BoundedContinuousFunction` sup-norm

The per-chart inner-disk sup `DiskChartCover.localCoeffMaxInner cover x om`
agrees with the `BoundedContinuousFunction` sup-norm of the inner-disk
restriction `localCoeffBcf cover om hx` from `DiskChartCoverArzela.lean`.

This bridge is the key step in turning the per-base-point
`BoundedContinuousFunction`-metric convergence produced by
`extract_diagonal_subseq` into convergence in the
`HolomorphicOneFormCoveredInner X cover` norm: the inner cover seminorm
is sup-over-basePoints of the BCF norm, so BCF convergence per chart
implies sup-of-BCF-norm-of-difference convergence (Finset sup' on a finite
set is continuous in each component), hence inner-cover-norm convergence.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff
open Set Metric HolomorphicOneForm BoundedContinuousFunction

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## `localCoeffBcf` norm = `localCoeffMaxInner`

Each side equals `sSup ‖localCoeff om x ·‖ '' (inner closed disk)`. -/

private lemma norm_localCoeffBcf_eq_localCoeffMaxInner
    (cover : DiskChartCover X) [Nonempty X] (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints) :
    ‖localCoeffBcf cover om hx‖ = localCoeffMaxInner cover x om := by
  -- mathlib's `BoundedContinuousFunction.norm_eq_iSup_norm` plus
  -- identification of the iSup with the image-sup we use for
  -- `localCoeffMaxInner`.
  rw [BoundedContinuousFunction.norm_eq_iSup_norm]
  -- Goal: `⨆ x_1, ‖(localCoeffBcf cover om hx) x_1‖
  --         = localCoeffMaxInner cover x om`.
  -- The BCF is the restriction of `‖localCoeff om x ·‖` to the
  -- subtype `closedBall ((chartAt ℂ x) x) (cover.innerRadius x)`.
  unfold localCoeffMaxInner
  -- RHS = `sSup ((‖localCoeff om x ·‖) '' closedBall ...)`.
  -- LHS = `⨆ (w : ↥closedBall ...), ‖localCoeff om x w.val‖`.
  -- These coincide via `sSup_image` / `iSup_subtype`.
  rw [show
      (⨆ x_1, ‖localCoeffBcf cover om hx x_1‖ : ℝ)
        = ⨆ (w : ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x))),
            ‖localCoeff om x w.val‖ from
        iSup_congr fun w => by rw [localCoeffBcf_apply]]
  rw [show
      sSup ((fun w => ‖localCoeff om x w‖) ''
            closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
        = sSup (Set.range (fun w :
            ↥(closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) =>
              ‖localCoeff om x w.val‖)) from ?_]
  · rfl
  · congr 1
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.val, w.property, rfl⟩

/-- Public form: the `BoundedContinuousFunction` norm of
`localCoeffBcf cover om hx` equals `localCoeffMaxInner cover x om`. -/
theorem norm_localCoeffBcf (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    ‖localCoeffBcf cover om hx‖ = localCoeffMaxInner cover x om :=
  norm_localCoeffBcf_eq_localCoeffMaxInner cover om hx

/-! ## Pointwise difference: BCF norm of difference equals
    `localCoeffMaxInner` of the difference. -/

theorem localCoeff_sub_bcf_eq (cover : DiskChartCover X) [Nonempty X]
    (om₁ om₂ : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    localCoeffBcf cover (om₁ - om₂) hx
      = localCoeffBcf cover om₁ hx - localCoeffBcf cover om₂ hx := by
  ext w
  show localCoeff (om₁ - om₂) x w.val =
    localCoeff om₁ x w.val - localCoeff om₂ x w.val
  have := HolomorphicOneForm.localCoeff_sub om₁ om₂ x
  rw [this]
  rfl

theorem norm_localCoeffBcf_sub (cover : DiskChartCover X) [Nonempty X]
    (om₁ om₂ : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints) :
    ‖localCoeffBcf cover om₁ hx - localCoeffBcf cover om₂ hx‖
      = localCoeffMaxInner cover x (om₁ - om₂) := by
  rw [← localCoeff_sub_bcf_eq, norm_localCoeffBcf]

end DiskChartCover

end JacobianChallenge

end
