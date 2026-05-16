/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicExtension
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Chart-pullback `AnalyticAt` on chart target (ZZ24)

For `f : MeromorphicNonzero X` and `z₀ : X`, the chart pullback
`f.chartPullback z₀ := (chartAt ℂ (f.toRiemannSphere z₀)) ∘ f.toRiemannSphere ∘
(chartAt ℂ z₀).symm` is `AnalyticAt` at every `w ∈ (chartAt ℂ z₀).target`
for which `f.toRiemannSphere ((chartAt ℂ z₀).symm w) ∈ (chartAt ℂ (f.toRiemannSphere z₀)).source`.

This is the chart-pullback-on-target analyticity bridge — needed for
chip 3d-19 (manifold f-regularity at Hurwitz fibre points) to discharge
its AnalyticAt hypothesis.

Proof:
* `(chartAt ℂ z₀).symm` is `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on `(chartAt ℂ z₀).target`
  (mathlib's `contMDiffOn_chart_symm`).
* `f.toRiemannSphere` is `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω` (in-tree).
* `(chartAt ℂ (f z₀))` is `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on its source.
* Composition gives `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f.chartPullback z₀) w`.
* `contMDiffAt_iff_contDiffAt` (both sides flat normed spaces, both ℂ).
* `ContDiffAt.analyticAt` for `ω`.

No `sorry`, no `axiom`. -/

open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Chart-pullback AnalyticAt on chart target.** -/
theorem chartPullback_analyticAt_of_chart_target
    (f : MeromorphicNonzero X) (z₀ : X)
    {w : ℂ} (hw_target : w ∈ (chartAt ℂ z₀).target)
    (hw_f_src : f.toRiemannSphere ((chartAt ℂ z₀).symm w)
      ∈ (chartAt ℂ (f.toRiemannSphere z₀)).source) :
    AnalyticAt ℂ (f.chartPullback z₀) w := by
  -- Step 1. `(chartAt ℂ z₀).symm` is ContMDiffAt at w (w in target open interior).
  have h_chart_symm_on :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ z₀).symm (chartAt ℂ z₀).target :=
    contMDiffOn_chart_symm
  have h_target_nhds : (chartAt ℂ z₀).target ∈ nhds w :=
    (chartAt ℂ z₀).open_target.mem_nhds hw_target
  have h_chart_symm_at : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ z₀).symm w :=
    (h_chart_symm_on w hw_target).contMDiffAt h_target_nhds
  -- Step 2. `f.toRiemannSphere` is ContMDiffAt at z := (chartAt ℂ z₀).symm w.
  have hf_at : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f.toRiemannSphere
      ((chartAt ℂ z₀).symm w) :=
    f.toRiemannSphere_contMDiff _
  -- Step 3. `(chartAt ℂ (f z₀))` is ContMDiffAt at f.toRiemannSphere (chart-symm w).
  have h_chart_on :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (f.toRiemannSphere z₀))
        (chartAt ℂ (f.toRiemannSphere z₀)).source :=
    contMDiffOn_chart
  have h_chart_src_nhds : (chartAt ℂ (f.toRiemannSphere z₀)).source ∈ nhds
      (f.toRiemannSphere ((chartAt ℂ z₀).symm w)) :=
    (chartAt ℂ (f.toRiemannSphere z₀)).open_source.mem_nhds hw_f_src
  have h_chart_at : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (chartAt ℂ (f.toRiemannSphere z₀))
      (f.toRiemannSphere ((chartAt ℂ z₀).symm w)) :=
    (h_chart_on _ hw_f_src).contMDiffAt h_chart_src_nhds
  -- Step 4. Compose: ContMDiffAt of f.chartPullback z₀ at w.
  have h_comp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f.chartPullback z₀) w := by
    show ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      ((chartAt ℂ (f.toRiemannSphere z₀)) ∘ f.toRiemannSphere
        ∘ (chartAt ℂ z₀).symm) w
    exact h_chart_at.comp w (hf_at.comp w h_chart_symm_at)
  -- Step 5. ContMDiffAt → ContDiffAt → AnalyticAt.
  have h_contDiffAt : ContDiffAt ℂ ω (f.chartPullback z₀) w :=
    contMDiffAt_iff_contDiffAt.mp h_comp
  exact h_contDiffAt.analyticAt

end MeromorphicNonzero
end JacobianChallenge

end
