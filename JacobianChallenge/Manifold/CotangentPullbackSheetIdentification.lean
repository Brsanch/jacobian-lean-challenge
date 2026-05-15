/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.LocalSheetDataUnique
import JacobianChallenge.Manifold.CotangentPullbackAtCongr
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheet
import JacobianChallenge.Manifold.MeromorphicNonzeroRegularValueSet
import JacobianChallenge.Manifold.MeromorphicNonzeroFiberFinite
import JacobianChallenge.Manifold.RiemannSphereRealManifold

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Cotangent pullback through a local sheet equals trace summand at the lifted point

For a non-constant `f : MeromorphicNonzero X`, a regular value
`v ∈ f.regularValueSet`, and a source-side sheet
`sheet_p := localSheetData_at_regular hnc hp_reg` (centered at some
fibre point `p` over a *different* base value `f.toRiemannSphere p`,
typically `β 0`), if `v ∈ sheet_p.V`, then `sheet_p.g v ∈ X` lies in
the fibre over `v`. The cotangent pullback through `sheet_p.g` at `v`
equals the cotangent pullback through `sheet_{q}.g`, where
`q := sheet_p.g v` and `sheet_q := localSheetData_at_regular hnc
(regular at q)`.

This is the substantive analytic identification that bridges the
chain-rule's source-indexed sum
`∑_{p ∈ sourceFiber} cotangentPullbackAt sheet_p.g (β(σ t)) ω`
to the value-indexed trace
`∑_{q ∈ fiberFinset(β(σ t))} cotangentPullbackAt sheet_q.g (β(σ t)) ω`
( = `traceAt(f)(β(σ t))(ω)`).

The proof: both `sheet_p.g` (as a local right-inverse near `v` with
`sheet_p.g v = q`) and `sheet_q.g` (as the canonical local inverse at
`q`) are local right-inverses passing through `q ∈ sheet_q.U`. By
`LocalSheetData.g_eventuallyEq_of_isLocalRightInverse`, they agree on
a neighbourhood of `v`, and `cotangentPullbackAt` is germ-determined
(`cotangentPullbackAt_congr_of_eventuallyEq`).

## What ships

* `MeromorphicNonzero.cotangentPullbackAt_localSheet_eq_at_target_sheet` —
  the cross-sheet identification at a regular value.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Cross-sheet cotangent pullback identification at a regular value.**

For source-side sheet `sheet_p` (centered at `p`) and target-side
sheet `sheet_q` (centered at `q := sheet_p.g v` over `v ∈ regularValueSet`),
the cotangent pullbacks at `v` agree.

Hypotheses:
* `hp_reg : p ∈ regularSet` — to define `sheet_p`.
* `hv : v ∈ regularValueSet` — to ensure `q := sheet_p.g v` lies in
  `regularSet` (via `mem_regularSet_of_preimage_regularValue`).
* `hv_in_Vp : v ∈ sheet_p.V` — to ensure `sheet_p.g` is defined and
  is a local right-inverse near `v`.

The hypothesis `v ∈ sheet_p.V` is the standard "sub-interval"
constraint of the chain-rule pathway: on a sub-interval of `t`, the
β-trace `β(σ t)` lies in `sheet_p.V` for every fibre point `p`, and
the chain-rule structural identity holds. -/
theorem cotangentPullbackAt_localSheet_eq_at_target_sheet
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : X} (hp_reg : p ∈ f.regularSet)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (hv_in_Vp : v ∈ (f.localSheetData_at_regular hnc hp_reg).V)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
        (f.localSheetData_at_regular hnc hp_reg).g v om
      = cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
        (f.localSheetData_at_regular hnc
          (f.mem_regularSet_of_preimage_regularValue hv
            ((f.localSheetData_at_regular hnc hp_reg).rightInvOn hv_in_Vp))).g v om := by
  -- Abbreviations (let-only; we won't fold the goal, just reason about
  -- s_p.g and s_q.g and convert at the end).
  let s_p : JacobianChallenge.LocalSheetData
      f.toRiemannSphere (f.toRiemannSphere p) p :=
    f.localSheetData_at_regular hnc hp_reg
  -- q := sheet_p.g v, with f.toRiemannSphere q = v.
  have hfq : f.toRiemannSphere (s_p.g v) = v := s_p.rightInvOn hv_in_Vp
  have hq_reg : s_p.g v ∈ f.regularSet :=
    f.mem_regularSet_of_preimage_regularValue hv hfq
  let s_q : JacobianChallenge.LocalSheetData
      f.toRiemannSphere (f.toRiemannSphere (s_p.g v)) (s_p.g v) :=
    f.localSheetData_at_regular hnc hq_reg
  -- We need:
  -- 1. v ∈ s_q.V — s_q.V is a nbhd of s_q.y₀ = f.toRiemannSphere (s_p.g v) = v.
  -- 2. s_p.g v ∈ s_q.U — s_p.g v is the center of s_q.
  -- 3. ContinuousAt s_p.g v — from s_p.g_continuousOn on the open V.
  -- 4. ∀ᶠ y' in 𝓝 v, f (s_p.g y') = y' — from s_p.rightInvOn on V.
  have h_s_q_V : v ∈ s_q.V := by
    -- s_q.V is a nbhd of s_q.y₀ = f.toRiemannSphere (s_p.g v) = v.
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
  -- Apply general uniqueness: s_p.g =ᶠ[𝓝 v] s_q.g.
  have h_eqOn : s_p.g =ᶠ[𝓝 v] s_q.g :=
    JacobianChallenge.LocalSheetData.g_eventuallyEq_of_isLocalRightInverse
      s_q h_s_q_V h_g_p_v h_g_p_cont h_g_p_rinv
  -- Cotangent pullback respects germ-equality.
  exact JacobianChallenge.cotangentPullbackAt_congr_of_eventuallyEq
    (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) h_eqOn om

/-- **Reformulation: the source-side cotangent pullback matches the
trace summand at the lifted point.**

When `v := β(σ t) ∈ sheet_p.V` (the sub-interval condition), the
source-side cotangent pullback `cotangentPullbackAt sheet_p.g v ω`
equals the trace summand at `q := sheet_p.g v`:
`cotangentPullbackAt sheet_q.g v ω`. -/
theorem cotangentPullbackAt_sourceSheet_eq_traceSummand
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : X} (hp_reg : p ∈ f.regularSet)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet)
    (hv_in_Vp : v ∈ (f.localSheetData_at_regular hnc hp_reg).V)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X) :
    let q : X := (f.localSheetData_at_regular hnc hp_reg).g v
    let hq_reg : q ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv
        ((f.localSheetData_at_regular hnc hp_reg).rightInvOn hv_in_Vp)
    cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
        (f.localSheetData_at_regular hnc hp_reg).g v om
      = cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
        (f.localSheetData_at_regular hnc hq_reg).g v om := by
  intros q hq_reg
  exact f.cotangentPullbackAt_localSheet_eq_at_target_sheet hnc hp_reg hv hv_in_Vp om

end MeromorphicNonzero

end JacobianChallenge

end
