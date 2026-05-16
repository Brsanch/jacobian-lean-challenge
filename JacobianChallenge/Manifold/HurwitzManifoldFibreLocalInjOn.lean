/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalBiholomorphism

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level local injectivity from planar InjOn

If the chart-pullback `f.chartPullback z₀ := (chartAt ℂ (f z₀)) ∘ f ∘
(chartAt ℂ z₀).symm` is `Set.InjOn` on `U ⊂ (chartAt ℂ z₀).target`,
and `f.toRiemannSphere` maps the source-side lift of `U` into
`(chartAt ℂ (f z₀)).source`, then `f.toRiemannSphere` is `Set.InjOn`
on the lift `(chartAt ℂ z₀).symm '' (U ∩ (chartAt ℂ z₀).target)`.

This is the **chart-coord ↔ manifold-coord lift of injectivity**. The
explicit chart-containment hypotheses are supplied by the caller
(small-disc continuity arguments around z₀).

No `sorry`, no `axiom`. -/

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold-level local injectivity** from planar InjOn of chart pullback. -/
theorem manifold_fibre_local_injOn
    (f : MeromorphicNonzero X) (z₀ : X)
    {U : Set ℂ}
    (_hU_target : U ⊆ (chartAt ℂ z₀).target)
    (h_planar_inj : Set.InjOn (f.chartPullback z₀) U) :
    Set.InjOn f.toRiemannSphere
      ((chartAt ℂ z₀).symm '' U) := by
  intro a ha b hb h_fa_eq_fb
  obtain ⟨wa, hwa, ha_eq⟩ := ha
  obtain ⟨wb, hwb, hb_eq⟩ := hb
  -- `(chartAt ℂ (f z₀)) (f a) = f.chartPullback z₀ wa`:
  have h_chart_a : f.chartPullback z₀ wa
      = (chartAt ℂ (f.toRiemannSphere z₀)) (f.toRiemannSphere a) := by
    show ((chartAt ℂ (f.toRiemannSphere z₀)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ z₀).symm) wa = _
    rw [Function.comp_apply, Function.comp_apply, ha_eq]
  have h_chart_b : f.chartPullback z₀ wb
      = (chartAt ℂ (f.toRiemannSphere z₀)) (f.toRiemannSphere b) := by
    show ((chartAt ℂ (f.toRiemannSphere z₀)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ z₀).symm) wb = _
    rw [Function.comp_apply, Function.comp_apply, hb_eq]
  -- From `f a = f b`, deduce `f.chartPullback z₀ wa = f.chartPullback z₀ wb`.
  have h_pullback_eq : f.chartPullback z₀ wa = f.chartPullback z₀ wb := by
    rw [h_chart_a, h_chart_b, h_fa_eq_fb]
  -- Apply planar InjOn.
  have hwa_eq_wb : wa = wb := h_planar_inj hwa hwb h_pullback_eq
  -- Conclude `a = b` from chart-symm.
  rw [← ha_eq, ← hb_eq, hwa_eq_wb]

end MeromorphicNonzero
end JacobianChallenge

end
