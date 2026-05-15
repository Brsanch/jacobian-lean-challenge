/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.DiskChartCoverSeminorm
import Mathlib.Analysis.Complex.Liouville

set_option diagnostics.threshold 100

/-! # Cauchy estimate for `localCoeff` on the inner disk

For each base point `x ∈ basePoints` and each `om : HolomorphicOneForm X`,
Cauchy's first-derivative estimate gives a uniform bound on
`deriv (localCoeff om x)` over the *inner* closed disk:

```
‖deriv (localCoeff om x) w‖
    ≤ localCoeffMax cover x om / (outerRadius x - innerRadius x)
```

for every `w ∈ closedBall ((chartAt ℂ x) x) (innerRadius x)`.

The proof uses mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
(Cauchy's estimate for the first derivative) with radius
`R := outerRadius x - dist w (chartAt ℂ x x)`. This radius is
positive since `dist w (chartAt ℂ x x) ≤ innerRadius x < outerRadius x`,
and the closed disk of radius `R` around `w` is contained in
`closedBall (chartAt ℂ x x) (outerRadius x) ⊆ (chartAt ℂ x).target`,
so `localCoeff om x` is analytic on a neighbourhood of the closed disk
of radius `R` around `w`. The Cauchy bound is `C / R` with `C ≤
localCoeffMax`, and `R ≥ outerRadius - innerRadius`.

Combined with the mean value theorem, this gives equicontinuity of the
family `{localCoeff om_n x | seminormVal om_n ≤ M}` on the inner disk —
the analytic input for Arzelà-Ascoli + diagonal subsequence
yielding Bolzano-Weierstrass for `HolomorphicOneForm X`.

No `sorry`, no `axiom`.
-/

open scoped Manifold Topology Bundle ContDiff Pointwise
open Set Metric HolomorphicOneForm

noncomputable section

namespace JacobianChallenge

namespace DiskChartCover

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Geometric helpers -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- For `w` in the inner closed disk, `dist w (chart center) ≤ innerRadius`. -/
private lemma dist_w_le_inner (cover : DiskChartCover X) {x : X}
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    dist w ((chartAt ℂ x) x) ≤ cover.innerRadius x := by
  rwa [mem_closedBall] at hw

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The Cauchy radius `R := outerRadius - dist w (center)` is positive
when `w` is in the inner closed disk. -/
private lemma cauchyRadius_pos (cover : DiskChartCover X) {x : X}
    (hx : x ∈ cover.basePoints) {w : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    0 < cover.outerRadius x - dist w ((chartAt ℂ x) x) := by
  have h_lt_inner := dist_w_le_inner cover hw
  have h_inner_lt_outer :=
    cover.innerRadius_lt_outerRadius x hx
  linarith

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The Cauchy radius is bounded below by `outerRadius - innerRadius`. -/
private lemma cauchyRadius_ge (cover : DiskChartCover X) {x : X}
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    cover.outerRadius x - cover.innerRadius x
      ≤ cover.outerRadius x - dist w ((chartAt ℂ x) x) := by
  have h := dist_w_le_inner cover hw
  linarith

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The closed ball of Cauchy radius `R` around `w` is contained in the
outer closed disk around the chart center (triangle inequality). -/
private lemma cauchyBall_closed_subset_outerBall (cover : DiskChartCover X)
    {x : X} {w : ℂ}
    (_hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    closedBall w (cover.outerRadius x - dist w ((chartAt ℂ x) x))
      ⊆ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) := by
  intro v hv
  rw [mem_closedBall] at hv ⊢
  calc dist v ((chartAt ℂ x) x)
      ≤ dist v w + dist w ((chartAt ℂ x) x) := dist_triangle _ _ _
    _ ≤ (cover.outerRadius x - dist w ((chartAt ℂ x) x))
          + dist w ((chartAt ℂ x) x) := add_le_add hv le_rfl
    _ = cover.outerRadius x := by ring

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The closed Cauchy ball is contained in the chart target. -/
private lemma cauchyBall_closed_subset_target (cover : DiskChartCover X)
    {x : X} (hx : x ∈ cover.basePoints) {w : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    closedBall w (cover.outerRadius x - dist w ((chartAt ℂ x) x))
      ⊆ (chartAt ℂ x).target :=
  (cauchyBall_closed_subset_outerBall cover hw).trans
    (cover.closedDisk_in_target x hx)

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The open Cauchy ball is contained in the chart target. -/
private lemma cauchyBall_open_subset_target (cover : DiskChartCover X)
    {x : X} (hx : x ∈ cover.basePoints) {w : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ball w (cover.outerRadius x - dist w ((chartAt ℂ x) x))
      ⊆ (chartAt ℂ x).target :=
  ball_subset_closedBall.trans (cauchyBall_closed_subset_target cover hx hw)

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The sphere of Cauchy radius is contained in the outer closed disk. -/
private lemma cauchySphere_subset_outerBall (cover : DiskChartCover X)
    {x : X} {w : ℂ}
    (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    sphere w (cover.outerRadius x - dist w ((chartAt ℂ x) x))
      ⊆ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
  sphere_subset_closedBall.trans (cauchyBall_closed_subset_outerBall cover hw)

/-! ## DiffContOnCl property on the Cauchy ball -/

/-- `localCoeff om x` is `DiffContOnCl` on the open Cauchy ball around
`w`: differentiable on the open ball, continuous on its closure. -/
private lemma localCoeff_diffContOnCl (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    DiffContOnCl ℂ (localCoeff om x)
      (ball w (cover.outerRadius x - dist w ((chartAt ℂ x) x))) := by
  refine ⟨?_, ?_⟩
  · exact (localCoeff_differentiableOn om x).mono
      (cauchyBall_open_subset_target cover hx hw)
  · -- closure of the open ball is the closed ball (in ℂ, since ℂ is a normed
    -- space with `r > 0`), and the closed ball is in the chart target where
    -- localCoeff is differentiable, hence continuous.
    have h_pos := cauchyRadius_pos cover hx hw
    have h_closure :
        closure (ball w (cover.outerRadius x - dist w ((chartAt ℂ x) x)))
          = closedBall w (cover.outerRadius x - dist w ((chartAt ℂ x) x)) :=
      closure_ball w h_pos.ne'
    rw [h_closure]
    have h_cont_target :
        ContinuousOn (localCoeff om x) (chartAt ℂ x).target :=
      (localCoeff_differentiableOn om x).continuousOn
    exact h_cont_target.mono (cauchyBall_closed_subset_target cover hx hw)

/-! ## Cauchy's first-derivative estimate -/

/-- **Cauchy's estimate for `localCoeff`**. For `w` in the inner closed
disk, the norm of `deriv (localCoeff om x) w` is bounded by
`localCoeffMax cover x om / (outerRadius x - dist w (chart center))`. -/
theorem norm_deriv_localCoeff_le_cauchyRadius (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖deriv (localCoeff om x) w‖
      ≤ localCoeffMax cover x om
          / (cover.outerRadius x - dist w ((chartAt ℂ x) x)) := by
  have h_pos := cauchyRadius_pos cover hx hw
  have h_diff := localCoeff_diffContOnCl cover om hx hw
  -- Bound on the sphere of Cauchy radius: by `localCoeffMax` since the sphere
  -- lies in the outer closed disk.
  have h_sphere :
      ∀ z ∈ sphere w (cover.outerRadius x - dist w ((chartAt ℂ x) x)),
        ‖localCoeff om x z‖ ≤ localCoeffMax cover x om := by
    intro z hz
    have hz_outer : z ∈ closedBall ((chartAt ℂ x) x) (cover.outerRadius x) :=
      cauchySphere_subset_outerBall cover hw hz
    exact norm_localCoeff_le_localCoeffMax cover om hx hz_outer
  -- Apply Cauchy's first-derivative estimate.
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le h_pos h_diff h_sphere

/-- **Uniform Cauchy bound on the inner disk.** The derivative is bounded
by `localCoeffMax / (outerRadius - innerRadius)` uniformly on the inner
closed disk. -/
theorem norm_deriv_localCoeff_le_innerDisk (cover : DiskChartCover X)
    (om : HolomorphicOneForm X) {x : X} (hx : x ∈ cover.basePoints)
    {w : ℂ} (hw : w ∈ closedBall ((chartAt ℂ x) x) (cover.innerRadius x)) :
    ‖deriv (localCoeff om x) w‖
      ≤ localCoeffMax cover x om
          / (cover.outerRadius x - cover.innerRadius x) := by
  have h_inner_lt :=
    cover.innerRadius_lt_outerRadius x hx
  have h_gap_pos : 0 < cover.outerRadius x - cover.innerRadius x := by linarith
  have h_cauchyRadius_pos := cauchyRadius_pos cover hx hw
  have h_step := norm_deriv_localCoeff_le_cauchyRadius cover om hx hw
  have h_ge := cauchyRadius_ge cover hw
  refine h_step.trans ?_
  -- localCoeffMax / (outer - dist) ≤ localCoeffMax / (outer - inner)
  -- via `div_le_div_of_nonneg_left` (with `b ≤ c → a / c ≤ a / b`).
  exact div_le_div_of_nonneg_left
    (localCoeffMax_nonneg cover om hx) h_gap_pos h_ge

end DiskChartCover

end JacobianChallenge

end
