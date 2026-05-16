/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HurwitzFibreLocalInjOn
import JacobianChallenge.Manifold.HurwitzManifoldFibreLocalInjOn
import JacobianChallenge.Manifold.HurwitzRegularSetFromInjOn

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Manifold-level f-regularity at Hurwitz fibre points

Packages chips 3d-16 (planar local injectivity), 3d-17 (manifold InjOn
lift), 3d-18 (regularSet membership from local InjOn) into:

  For a planar point `w = φ(ζ^j · ξ)` in the chart target with the
  chart-pullback analytic and having non-zero derivative there, the
  manifold point `(chartAt ℂ z₀).symm w` lies in `f.regularSet`.

Uses `OpenPartialHomeomorph.isOpen_image_symm_of_subset_target` to
package the chart-symm image as an open neighbourhood.

No `sorry`, no `axiom`. -/

open Filter Topology Set
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge
namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Manifold f-regularity at a Hurwitz fibre point.**

For `g := f.chartPullback z₀`, a point `w ∈ (chartAt ℂ z₀).target` with
`AnalyticAt ℂ g w` and `deriv g w ≠ 0`, the lifted manifold point
`(chartAt ℂ z₀).symm w` is in `f.regularSet`. -/
theorem manifold_fibre_regular_at_chart_point
    (f : MeromorphicNonzero X) (z₀ : X)
    {w : ℂ}
    (h_target : w ∈ (chartAt ℂ z₀).target)
    (h_g_an : AnalyticAt ℂ (f.chartPullback z₀) w)
    (h_g_deriv_ne : deriv (f.chartPullback z₀) w ≠ 0) :
    (chartAt ℂ z₀).symm w ∈ f.regularSet := by
  -- 1. Planar local biholomorphism gives U ∈ 𝓝 w with InjOn (f.chartPullback z₀) U.
  obtain ⟨U, hU_nhds, _V, _hV_nhds, _φ_inv, _hMt_uv, _hMt_vu, hLeftInv, _hRightInv,
          _hφ_inv_an⟩ :=
    JacobianChallenge.Manifold.AnalyticAt.exists_local_biholomorphism
      h_g_an h_g_deriv_ne
  have h_planar_inj : Set.InjOn (f.chartPullback z₀) U := hLeftInv.injOn
  -- 2. Shrink U to U' := U ∩ (chartAt ℂ z₀).target, still a 𝓝 of w.
  obtain ⟨U_open, hU_open_sub, hU_open_isOpen, hw_in_U_open⟩ :=
    mem_nhds_iff.mp hU_nhds
  set U' := U_open ∩ (chartAt ℂ z₀).target with hU'_def
  have hU'_isOpen : IsOpen U' :=
    hU_open_isOpen.inter (chartAt ℂ z₀).open_target
  have hw_in_U' : w ∈ U' := ⟨hw_in_U_open, h_target⟩
  have hU'_sub_U : U' ⊆ U := fun _ hx => hU_open_sub hx.1
  have hU'_sub_target : U' ⊆ (chartAt ℂ z₀).target := fun _ hx => hx.2
  have hU'_inj : Set.InjOn (f.chartPullback z₀) U' :=
    h_planar_inj.mono hU'_sub_U
  -- 3. `(chartAt ℂ z₀).symm '' U'` is open (via `isOpen_image_symm_of_subset_target`).
  set W : Set X := (chartAt ℂ z₀).symm '' U' with hW_def
  have h_W_open : IsOpen W :=
    (chartAt ℂ z₀).isOpen_image_symm_of_subset_target hU'_isOpen hU'_sub_target
  -- 4. W contains the lifted point.
  have h_lift_in_W : (chartAt ℂ z₀).symm w ∈ W := ⟨w, hw_in_U', rfl⟩
  -- 5. Apply chip 3d-17 (with junk hypotheses).
  have h_manifold_inj : Set.InjOn f.toRiemannSphere W :=
    f.manifold_fibre_local_injOn z₀ hU'_sub_target hU'_inj
  -- 6. Apply chip 3d-18.
  exact f.mem_regularSet_of_local_injOn ⟨W, h_W_open.mem_nhds h_lift_in_W, h_manifold_inj⟩

end MeromorphicNonzero
end JacobianChallenge

end
