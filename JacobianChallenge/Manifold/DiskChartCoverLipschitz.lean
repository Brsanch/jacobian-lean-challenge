/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverCauchyEstimate
import JacobianChallenge.Manifold.DiskChartCoverSeminormAggregate
import Mathlib.Analysis.Calculus.MeanValue

set_option diagnostics.threshold 100

/-! # Lipschitz bound for `localCoeff` on the inner disk

For each base point `x ∈ basePoints` and each `om : HolomorphicOneForm X`,
the mean-value inequality combined with Cauchy's first-derivative
estimate (chip 4) gives a uniform *Lipschitz bound* on `localCoeff om x`
over the inner closed disk:

```
‖localCoeff om x w - localCoeff om x w'‖ ≤ L * ‖w - w'‖
```

with Lipschitz constant `L := localCoeffMax cover x om / (outerRadius x
- innerRadius x)` for every `w, w' ∈ closedBall ((chartAt ℂ x) x)
(innerRadius x)`.

This is the **equicontinuity input** for the upcoming Arzelà-Ascoli +
diagonal subsequence argument yielding Bolzano-Weierstrass for
`HolomorphicOneForm X`.

The proof uses mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`
applied to the convex closed ball, with the chip 4 bound on the
fderiv (which equals the deriv as scalar multiplication, with
matching operator norm for ℂ → ℂ).

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## ℂ-differentiability gives `HasFDerivWithinAt` -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The inner closed disk is convex (in the real sense, as a subset of ℂ ≃ ℝ²). -/
private lemma innerDisk_convex (cover : DiskChartCover X) (x : X) :
    Convex ℝ (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :=
  convex_closedBall _ _

/-- `localCoeff om x` has the `HasFDerivWithinAt` form expected by
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`, with the
fderiv given by `fderiv ℂ (localCoeff om x) w` (the complex
linearization). -/
private lemma localCoeff_hasFDerivWithinAt (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    HasFDerivWithinAt (localCoeff om x)
      (fderiv ℂ (localCoeff om x) w)
      (closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) w := by
  have h_diff_at : DifferentiableAt ℂ (localCoeff om x) w := by
    have h_inner_le_outer :
        cover.innerRadius x ≤ cover.outerRadius x :=
      le_of_lt (cover.innerRadius_lt_outerRadius x hx)
    have hw_outer :
        w ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
      (closedBall_subset_closedBall h_inner_le_outer) hw
    -- localCoeff_differentiableOn gives DifferentiableOn on chart.target;
    -- chart.target ⊇ closedBall(outerRadius), and closedBall(outerRadius)
    -- is in the *interior* of chart.target (since chart.target is open),
    -- so we get DifferentiableAt at any point in closedBall.
    have h_in_target :
        w ∈ (chartAt ℂ x).target :=
      cover.closedDisk_in_target x hx hw_outer
    have h_diff_on : DifferentiableOn ℂ (localCoeff om x) (chartAt ℂ x).target :=
      localCoeff_differentiableOn om x
    exact h_diff_on.differentiableAt
      ((chartAt ℂ x).open_target.mem_nhds h_in_target)
  exact h_diff_at.hasFDerivAt.hasFDerivWithinAt

/-- The fderiv at `w` of `localCoeff om x` has operator norm bounded by
`localCoeffMax cover x om / (outerRadius x - innerRadius x)` for
`w ∈ closedBall (innerRadius x)`. -/
private lemma norm_fderiv_localCoeff_le_innerDisk
    (cover : DiskChartCover X) (om : HolomorphicOneForm X)
    {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖fderiv ℂ (localCoeff om x) w‖
      ≤ localCoeffMax cover x om
          / (cover.outerRadius x - cover.innerRadius x) := by
  rw [← norm_deriv_eq_norm_fderiv]
  exact norm_deriv_localCoeff_le_innerDisk cover om hx hw

/-! ## Lipschitz bound -/

/-- **Lipschitz bound on the inner disk.** For each base point `x` and
each `om : HolomorphicOneForm X`, the function `localCoeff om x` is
Lipschitz on the inner closed disk with constant
`localCoeffMax cover x om / (outerRadius x - innerRadius x)`. -/
theorem localCoeff_lipschitz_innerDisk (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w w' : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
    (hw' : w' ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖localCoeff om x w - localCoeff om x w'‖
      ≤ localCoeffMax cover x om
          / (cover.outerRadius x - cover.innerRadius x) * ‖w - w'‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun u => fderiv ℂ (localCoeff om x) u)
    (s := closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
    (fun u hu => localCoeff_hasFDerivWithinAt cover om hx hu)
    (fun u hu => norm_fderiv_localCoeff_le_innerDisk cover om hx hu)
    (innerDisk_convex cover x) hw' hw

/-- **Lipschitz bound via seminorm.** For `om` with `seminormVal ≤ M`,
the Lipschitz bound becomes `M / (outerRadius x - innerRadius x)`. -/
theorem localCoeff_lipschitz_innerDisk_of_seminorm_le
    (cover : DiskChartCover X) [Nonempty X]
    (om : HolomorphicOneForm X) (M : ℝ) (hM : seminormVal cover om ≤ M)
    {x : X} (hx : x ∈ cover.basePoints)
    {w w' : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x))
    (hw' : w' ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖localCoeff om x w - localCoeff om x w'‖
      ≤ M / (cover.outerRadius x - cover.innerRadius x) * ‖w - w'‖ := by
  have h_step := localCoeff_lipschitz_innerDisk cover om hx hw hw'
  have h_localCoeffMax_le : localCoeffMax cover x om ≤ M := by
    have h_le_seminormVal :
        localCoeffMax cover x om
          ≤ cover.basePoints.sup' cover.basePoints_nonempty
              (fun y => localCoeffMax cover y om) :=
      Finset.le_sup' (fun y => localCoeffMax cover y om) hx
    exact h_le_seminormVal.trans hM
  have h_inner_lt :=
    cover.innerRadius_lt_outerRadius x hx
  have h_gap_pos : 0 < cover.outerRadius x - cover.innerRadius x := by linarith
  have h_norm_nonneg : 0 ≤ ‖w - w'‖ := norm_nonneg _
  refine h_step.trans ?_
  apply mul_le_mul_of_nonneg_right _ h_norm_nonneg
  exact div_le_div_of_nonneg_right h_localCoeffMax_le h_gap_pos.le

end DiskChartCover

end JacobianChallenge

end
