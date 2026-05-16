/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolomorphicCotangentPullbackAt
import JacobianChallenge.Manifold.MeromorphicNonzeroTraceAt
import JacobianChallenge.Manifold.LocalSheetDataUnique

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Pointwise holomorphic trace `f_*α` at a regular value

Holomorphic-side analogue of `traceAt`
(`Manifold/MeromorphicNonzeroTraceAt.lean`). For
`f : MeromorphicNonzero X` non-constant and `v ∈ f.regularValueSet`,
the **holomorphic trace** of `α : HolomorphicOneForm X` at `v` is the
finite sum

  `holTraceAt f hnc v hv α := Σ_{p ∈ f⁻¹(v)} holCotangentPullbackAt sheet_p.g v α`

where `sheet_p` is the local biholomorphism at the fibre point `p`.
Each summand is a `CotangentSpace 𝓘(ℂ, ℂ) v`-valued contribution.

ℂ-linearity in α descends pointwise from `holCotangentPullbackAt_{zero,
add, smul}` + `Finset.sum_{zero, add, smul}`.

Companion ships:

* `holSheetCotPullback` — wrapper for `holCotangentPullbackAt` at the
  source-side sheet inverse, parallel to `sheetCotPullback` in
  `Manifold/SourceSheetSumEqTraceAt.lean`.
* `holTraceAt_eq_sum_holSheetCotPullback` — trace = source-fibre sum of
  `holSheetCotPullback`, by definitional unfolding.
* `holCotangentPullbackAt_localSheet_eq_at_target_sheet` — cross-sheet
  identification at a regular value, parallel to
  `cotangentPullbackAt_localSheet_eq_at_target_sheet` in
  `Manifold/CotangentPullbackSheetIdentification.lean`. Reuses
  `LocalSheetData.g_eventuallyEq_of_isLocalRightInverse` (model-generic)
  + `holCotangentPullbackAt_congr_of_eventuallyEq`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Pointwise holomorphic trace `f_*α` at a regular value `v`.**
Finite sum of per-sheet holomorphic cotangent pullbacks over the fibre
`f⁻¹({v})`. -/
noncomputable def holTraceAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (α : HolomorphicOneForm X) :
    CotangentSpace 𝓘(ℂ, ℂ) v := by
  classical
  exact ∑ p ∈ (f.fiberFinset hv).attach,
    holCotangentPullbackAt
      (f.localSheetData_at_regular hnc
        (f.mem_regularSet_of_preimage_regularValue hv
          ((f.mem_fiberFinset_iff hv p.val).mp p.property))).g
      v α

/-! ## ℂ-linearity in the 1-form -/

@[simp] lemma holTraceAt_zero
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) :
    f.holTraceAt hnc hv (0 : HolomorphicOneForm X) = 0 := by
  unfold holTraceAt
  simp [holCotangentPullbackAt_zero]

@[simp] lemma holTraceAt_add
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (α₁ α₂ : HolomorphicOneForm X) :
    f.holTraceAt hnc hv (α₁ + α₂)
      = f.holTraceAt hnc hv α₁ + f.holTraceAt hnc hv α₂ := by
  classical
  unfold holTraceAt
  simp only [holCotangentPullbackAt_add]
  exact Finset.sum_add_distrib

@[simp] lemma holTraceAt_smul
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (c : ℂ) (α : HolomorphicOneForm X) :
    f.holTraceAt hnc hv (c • α) = c • f.holTraceAt hnc hv α := by
  classical
  unfold holTraceAt
  simp only [holCotangentPullbackAt_smul]
  exact Finset.smul_sum.symm

/-! ## Source-side wrapper -/

/-- **Wrapper for source-side holomorphic cotangent pullback at a sheet
inverse.** Parallel to `sheetCotPullback` for the realified case. -/
noncomputable def holSheetCotPullback
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {x₀ : X} (hx_reg : x₀ ∈ f.regularSet)
    (v : RiemannSphere) (α : HolomorphicOneForm X) :
    CotangentSpace 𝓘(ℂ, ℂ) v :=
  holCotangentPullbackAt
    (f.localSheetData_at_regular hnc hx_reg).g v α

/-- **`holTraceAt` rewritten via `holSheetCotPullback`.** Definitional
unfolding: the holomorphic trace at a regular value is the source-fibre
sum of `holSheetCotPullback` over local sheets at fibre points. -/
lemma holTraceAt_eq_sum_holSheetCotPullback
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (α : HolomorphicOneForm X) :
    f.holTraceAt hnc hv α
      = ∑ p ∈ (f.fiberFinset hv).attach,
          f.holSheetCotPullback hnc
            (f.mem_regularSet_of_preimage_regularValue hv
              ((f.mem_fiberFinset_iff hv p.val).mp p.property))
            v α := by
  unfold holTraceAt holSheetCotPullback
  rfl

/-! ## Cross-sheet identification (holomorphic) -/

/-- **Cross-sheet holomorphic cotangent pullback identification at a
regular value.** Parallel to
`cotangentPullbackAt_localSheet_eq_at_target_sheet` but for the
holomorphic bundle. Reuses the model-generic uniqueness
`LocalSheetData.g_eventuallyEq_of_isLocalRightInverse` and the new
`holCotangentPullbackAt_congr_of_eventuallyEq`. -/
theorem holCotangentPullbackAt_localSheet_eq_at_target_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : X} (hp_reg : p ∈ f.regularSet)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (hv_in_Vp : v ∈ (f.localSheetData_at_regular hnc hp_reg).V)
    (α : HolomorphicOneForm X) :
    holCotangentPullbackAt
        (f.localSheetData_at_regular hnc hp_reg).g v α
      = holCotangentPullbackAt
        (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue hv
            ((f.localSheetData_at_regular hnc hp_reg).rightInvOn hv_in_Vp))).g
        v α := by
  -- Setup (mirrors the realified proof exactly).
  let s_p : JacobianChallenge.LocalSheetData
      f.toRiemannSphere (f.toRiemannSphere p) p :=
    f.localSheetData_at_regular hnc hp_reg
  have hfq : f.toRiemannSphere (s_p.g v) = v := s_p.rightInvOn hv_in_Vp
  have hq_reg : s_p.g v ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hv hfq
  let s_q : JacobianChallenge.LocalSheetData
      f.toRiemannSphere (f.toRiemannSphere (s_p.g v)) (s_p.g v) :=
    f.localSheetData_at_regular hnc hq_reg
  have h_s_q_V : v ∈ s_q.V := by
    have h_mem : f.toRiemannSphere (s_p.g v) ∈ s_q.V := s_q.mem_V
    exact Eq.subst (motive := fun w => w ∈ s_q.V) hfq h_mem
  have h_g_p_v : s_p.g v ∈ s_q.U := s_q.mem_U
  have hVp_nhds : s_p.V ∈ 𝓝 v := s_p.V_open.mem_nhds hv_in_Vp
  have h_g_p_cont : ContinuousAt s_p.g v := by
    have h_within : ContinuousWithinAt s_p.g s_p.V v := s_p.g_continuousOn v hv_in_Vp
    rwa [continuousWithinAt_iff_continuousAt hVp_nhds] at h_within
  have h_g_p_rinv : ∀ᶠ y' in 𝓝 v, f.toRiemannSphere (s_p.g y') = y' := by
    filter_upwards [hVp_nhds] with y' hy'_V
    exact s_p.rightInvOn hy'_V
  have h_eqOn : s_p.g =ᶠ[𝓝 v] s_q.g :=
    JacobianChallenge.LocalSheetData.g_eventuallyEq_of_isLocalRightInverse
      s_q h_s_q_V h_g_p_v h_g_p_cont h_g_p_rinv
  exact JacobianChallenge.holCotangentPullbackAt_congr_of_eventuallyEq h_eqOn α

end MeromorphicNonzero

end JacobianChallenge

end
