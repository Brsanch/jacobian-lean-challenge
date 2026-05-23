/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option linter.unusedSectionVars false

/-! # Foundational lemma: chart-symm composition lift at `C^∞` regularity

For a smooth `g_smooth : ℝ → ℂ` whose image lies in `φ.target` for a
chart `φ ∈ atlas ℂ X`, the lift `g := φ.symm ∘ g_smooth` is
`ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ⊤` on the manifold.

The regularity is `C^∞` (= `⊤` in mathlib's `WithTop ℕ∞`), matching the
regularity of `SmoothPath` and `Smooth2Chain` in tree — analytic (`ω`)
regularity is explicitly avoided per the `SmoothPath` docstring
("analytic functions are germ-determined and cannot in general be glued
across charts").

The **scalar-field model is `ℝ`** throughout the manifold side
(`𝓘(ℝ, ℂ)`), matching `SmoothPath`'s convention. A complex 1-manifold
`[ChartedSpace ℂ X]` with `[IsManifold (𝓘(ℝ, ℂ)) ⊤ X]` admits this
real-model use of the same chart atlas.

This is the structural foundation for the T4 reverse-leg Whitney
approximation arc (per `T4_WHITNEY_PLAN.md`). It composes downstream with
mathlib's `Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`
(smooth approx in `ℝ → ℂ`) + compactness + Tietze extension to give
the full chart-contained Whitney result.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Metric

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (𝓘(ℝ, ℂ)) ⊤ X]

/-- **`φ.symm` is `ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤` on `φ.target`**
for any chart `φ ∈ atlas ℂ X` (real-model regularity). Direct from
`contMDiffOn_symm_of_mem_maximalAtlas` in the `𝓘(ℝ, ℂ)` model. -/
theorem chartSymm_contMDiffOn
    (φ : OpenPartialHomeomorph X ℂ) (h_atlas : φ ∈ atlas ℂ X) :
    ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤
      (φ.symm : ℂ → X) φ.target :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas h_atlas)

/-- **Chart-target lift.** For a `C^∞`-smooth `g_smooth : ℝ → ℂ` whose
image lies in `φ.target`, the manifold-side composition
`t ↦ φ.symm (g_smooth t)` is `ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ⊤`. -/
theorem contMDiff_chartSymm_comp_of_contDiff_target
    {φ : OpenPartialHomeomorph X ℂ} (h_atlas : φ ∈ atlas ℂ X)
    {g_smooth : ℝ → ℂ} (hg_smooth : ContDiff ℝ ⊤ g_smooth)
    (h_target : ∀ t : ℝ, g_smooth t ∈ φ.target) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ⊤
      (fun t : ℝ => φ.symm (g_smooth t)) := by
  have h_g_smooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ⊤ g_smooth :=
    hg_smooth.contMDiff
  have h_symm_smooth : ContMDiffOn (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤
      (φ.symm : ℂ → X) φ.target :=
    chartSymm_contMDiffOn φ h_atlas
  intro t
  have h_g_at : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ⊤ g_smooth t := h_g_smooth t
  have h_g_t_mem : g_smooth t ∈ φ.target := h_target t
  have h_symm_at : ContMDiffAt (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ⊤
      (φ.symm : ℂ → X) (g_smooth t) :=
    (h_symm_smooth (g_smooth t) h_g_t_mem).contMDiffAt
      (φ.open_target.mem_nhds h_g_t_mem)
  exact h_symm_at.comp t h_g_at

/-- **Manifold-side membership.** Image of the chart-symm lift lies in
`φ.source` for all `t`. -/
theorem chartSymm_comp_mem_source
    {φ : OpenPartialHomeomorph X ℂ} {g_smooth : ℝ → ℂ}
    (h_target : ∀ t : ℝ, g_smooth t ∈ φ.target) :
    ∀ t : ℝ, (φ.symm (g_smooth t) : X) ∈ φ.source := by
  intro t
  exact φ.map_target (h_target t)

/-- **Chart-distance bound preserved by lift.** Chart-pullback of the
lift recovers `g_smooth`. Hence chart-distance bounds on `g_smooth`
translate verbatim to chart-distance bounds on `φ.symm ∘ g_smooth`. -/
theorem chartPullback_of_chartSymm_comp_eq
    {φ : OpenPartialHomeomorph X ℂ} {g_smooth : ℝ → ℂ}
    (h_target : ∀ t : ℝ, g_smooth t ∈ φ.target) :
    ∀ t : ℝ, (φ : X → ℂ) (φ.symm (g_smooth t)) = g_smooth t := by
  intro t
  exact φ.right_inv (h_target t)

end JacobianChallenge

end
