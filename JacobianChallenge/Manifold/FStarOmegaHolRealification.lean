/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.HolCotangentPullbackRealification
import JacobianChallenge.Manifold.MeromorphicNonzeroHolTraceAt
import JacobianChallenge.Manifold.MeromorphicNonzeroFStarOmegaHolDef
import JacobianChallenge.Manifold.MeromorphicNonzeroFStarOmegaDef
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAt
import JacobianChallenge.Manifold.MeromorphicNonzeroLocalSheetSmooth
import JacobianChallenge.Manifold.SmoothPathIntegral

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! # Realification compatibility for `fStarOmegaHol` (trace-sum level)

The trace-level realification identity. For every regular value `v` and
tangent vector `w : ℂ`:

  `(realPartCLM (f.fStarOmegaHol hnc α v)) w
     = SmoothPath.applyCotangent (f.fStarOmega hnc (realComponent α) v) w`

Combined with the on-regular-set holomorphic 1-form `fStarOmegaHolOn`
(2026-05-20 afternoon arc), this gives the realification side of
`HolomorphicTraceExtension`. Together with item (2) of the closure
plan (extension across critical values, n-th-root + Riemann removable
sing), `HolomorphicTraceExtension X` would be unconditional.

## Proof

Apply both sides to `w`. Both reduce to a Finset sum over the fiber.
The LHS uses `realPartCLM` ℝ-linear over the sum; the RHS unfolds
`applyCotangent` to the apply of `cotangentEquiv` (also ℝ-linear).
Per-summand equality is `realPartCLM_holCotangentPullbackAt_apply`
(`HolCotangentPullbackRealification.lean`).

We unfold the sum via `Finset.induction_on` to avoid pattern-matching
issues with `map_sum realPartCLM` on the `CotangentSpace`-typed sum
(see CHANGELOG note for `HolCotangentPullbackRealification.lean`).

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

/-- **`MDifferentiableAt` of the local sheet `g` at a fiber value.**
Substitutes `v = f.toRiemannSphere p` to apply the basepoint
smoothness; avoids the `LocalSheetData`-dependent-type rewrite issue
that blocks `rw [hp_to_v]` directly. -/
private theorem mdifferentiableAt_localSheet_g_at_value
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {p : X} (hp_reg : p ∈ f.regularSet)
    {v : RiemannSphere} (hp_to_v : f.toRiemannSphere p = v) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (f.localSheetData_at_regular hnc hp_reg).g v := by
  subst hp_to_v
  exact (f.contMDiffAt_localSheet_g_at_basePoint hnc hp_reg).mdifferentiableAt
    (by decide)

/-- **Realification compatibility, apply-level, real side.** -/
theorem realPartCLM_fStarOmegaHol_apply
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) (w : ℂ) :
    (realPartCLM (f.fStarOmegaHol hnc α v)) w
      = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
          (f.fStarOmega hnc (realComponent α) v) w := by
  classical
  -- Reduce both traces to fiber-finset sums.
  rw [f.fStarOmegaHol_apply_of_regular hnc α hv,
      f.fStarOmega_apply_of_regular hnc (realComponent α) hv]
  rw [f.holTraceAt_eq_sum_holSheetCotPullback hnc hv α,
      f.traceAt_eq_sum_sheetCotPullback hnc hv (realComponent α)]
  -- Per-summand realification compatibility (chip 2).
  -- We sum via induction over the Finset.
  have h_per_sheet : ∀ p ∈ (f.fiberFinset hv).attach,
      (realPartCLM (f.holSheetCotPullback hnc
        (f.mem_regularSet_of_preimage_regularValue hv
          ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v α)) w
        = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv
                ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v
              (realComponent α)) w := by
    intro p _
    have hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv
        ((f.mem_fiberFinset_iff hv p.val).mp p.property)
    have hp_to_v : f.toRiemannSphere p.val = v :=
      (f.mem_fiberFinset_iff hv p.val).mp p.property
    have h_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (f.localSheetData_at_regular hnc hp_reg).g v :=
      mdifferentiableAt_localSheet_g_at_value f hnc hp_reg hp_to_v
    -- Unfold sheetCotPullback / holSheetCotPullback to cotangentPullbackAt.
    show (realPartCLM (f.holSheetCotPullback hnc hp_reg v α)) w
      = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
          (f.sheetCotPullback hnc hp_reg v (realComponent α)) w
    unfold holSheetCotPullback sheetCotPullback
    -- Apply chip 2.
    rw [realPartCLM_holCotangentPullbackAt_apply h_mdiff α w]
    -- RHS: applyCotangent (cotangentPullbackAt _ (realComponent α)) w
    -- = ((realComponent α).toFun (g v)).comp (mfderiv 𝓘(ℝ,ℂ) g v) w
    -- = ((realComponent α).toFun (g v)) (mfderiv 𝓘(ℝ,ℂ) g v w)
    -- = (realPartCLM (α.eval (g v))) (mfderiv 𝓘(ℝ,ℂ) g v w)
    -- = Complex.re (α.eval (g v) (mfderiv 𝓘(ℝ,ℂ) g v w))
    unfold SmoothPath.applyCotangent
    -- cotangentEquiv at v is id-on-data; cotangentPullbackAt g v (realComponent α) is the comp.
    show Complex.re ((α.eval _) ((mfderiv _ _ _ _) w))
      = (SmoothPath.cotangentEquiv
          (cotangentPullbackAt (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
            (f.localSheetData_at_regular hnc hp_reg).g v (realComponent α))) w
    -- cotangentEquiv = id-on-data.
    unfold cotangentPullbackAt
    show Complex.re ((α.eval ((f.localSheetData_at_regular hnc hp_reg).g v))
        ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
          (f.localSheetData_at_regular hnc hp_reg).g v) w))
      = (SmoothPath.cotangentEquiv
          (((realComponent α).toFun
            ((f.localSheetData_at_regular hnc hp_reg).g v)).comp
              (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
                (f.localSheetData_at_regular hnc hp_reg).g v))) w
    -- cotangentEquiv φ = φ definitionally (id-on-data).
    show Complex.re ((α.eval ((f.localSheetData_at_regular hnc hp_reg).g v))
        ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
          (f.localSheetData_at_regular hnc hp_reg).g v) w))
      = (((realComponent α).toFun
          ((f.localSheetData_at_regular hnc hp_reg).g v)).comp
            (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc hp_reg).g v)) w
    -- Unfold ((realComponent α).toFun x) = realPartCLM (α.eval x).
    have h_realComp :
        (realComponent α).toFun ((f.localSheetData_at_regular hnc hp_reg).g v)
          = realPartCLM (α.eval ((f.localSheetData_at_regular hnc hp_reg).g v)) :=
      (realPartCLM_eval α _).symm
    rw [h_realComp]
    -- Now RHS = realPartCLM (α.eval _) ∘L mfderiv applied to w = realPartCLM (α.eval _) (mfderiv w)
    -- = Complex.re (α.eval _ (mfderiv w)). Same as LHS by rfl on Complex.re ∘ realPartCLM_apply_value.
    show Complex.re ((α.eval ((f.localSheetData_at_regular hnc hp_reg).g v))
        ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
          (f.localSheetData_at_regular hnc hp_reg).g v) w))
      = (realPartCLM (α.eval ((f.localSheetData_at_regular hnc hp_reg).g v)))
          ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
            (f.localSheetData_at_regular hnc hp_reg).g v) w)
    rw [realPartCLM_apply]
    rfl
  -- General lemma: any finset and any per-summand hypothesis.
  have general : ∀ (S : Finset { x // x ∈ f.fiberFinset hv })
      (h_each : ∀ p ∈ S,
        (realPartCLM (f.holSheetCotPullback hnc
          (f.mem_regularSet_of_preimage_regularValue hv
            ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v α)) w
          = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
              (f.sheetCotPullback hnc
                (f.mem_regularSet_of_preimage_regularValue hv
                  ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v
                (realComponent α)) w),
      (realPartCLM (∑ p ∈ S, f.holSheetCotPullback hnc
        (f.mem_regularSet_of_preimage_regularValue hv
          ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v α)) w
        = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
            (∑ p ∈ S, f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv
                ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v
              (realComponent α)) w := by
    intro S h_each
    induction S using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, map_zero, ContinuousLinearMap.zero_apply]
        unfold SmoothPath.applyCotangent
        simp only [map_zero, ContinuousLinearMap.zero_apply]
    | insert q s hq ih =>
        rw [Finset.sum_insert hq, Finset.sum_insert hq]
        rw [show
            realPartCLM (_ + _)
              = realPartCLM (f.holSheetCotPullback hnc
                  (f.mem_regularSet_of_preimage_regularValue hv
                    ((f.mem_fiberFinset_iff hv q.val).mp q.property)) v α)
                + realPartCLM (∑ x ∈ s, f.holSheetCotPullback hnc
                    (f.mem_regularSet_of_preimage_regularValue hv
                      ((f.mem_fiberFinset_iff hv x.val).mp x.property)) v α) from
          map_add realPartCLM _ _]
        rw [ContinuousLinearMap.add_apply]
        unfold SmoothPath.applyCotangent
        rw [show
            SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ)) (_ + _)
              = SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ))
                  (f.sheetCotPullback hnc
                    (f.mem_regularSet_of_preimage_regularValue hv
                      ((f.mem_fiberFinset_iff hv q.val).mp q.property)) v
                    (realComponent α))
                + SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ))
                    (∑ x ∈ s, f.sheetCotPullback hnc
                      (f.mem_regularSet_of_preimage_regularValue hv
                        ((f.mem_fiberFinset_iff hv x.val).mp x.property)) v
                      (realComponent α)) from
          map_add (SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ))) _ _]
        rw [ContinuousLinearMap.add_apply]
        rw [h_each q (Finset.mem_insert_self q s)]
        congr 1
        have ih' := ih (fun p hp => h_each p (Finset.mem_insert_of_mem hp))
        unfold SmoothPath.applyCotangent at ih'
        exact ih'
  exact general (f.fiberFinset hv).attach h_per_sheet

/-- **Realification compatibility, apply-level, imaginary side.** -/
theorem imagPartCLM_fStarOmegaHol_apply
    [DecidableEq X]
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    (α : HolomorphicOneForm X)
    {v : RiemannSphere} (hv : v ∈ f.regularValueSet) (w : ℂ) :
    (imagPartCLM (f.fStarOmegaHol hnc α v)) w
      = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
          (f.fStarOmega hnc (imagComponent α) v) w := by
  classical
  rw [f.fStarOmegaHol_apply_of_regular hnc α hv,
      f.fStarOmega_apply_of_regular hnc (imagComponent α) hv]
  rw [f.holTraceAt_eq_sum_holSheetCotPullback hnc hv α,
      f.traceAt_eq_sum_sheetCotPullback hnc hv (imagComponent α)]
  have h_per_sheet : ∀ p ∈ (f.fiberFinset hv).attach,
      (imagPartCLM (f.holSheetCotPullback hnc
        (f.mem_regularSet_of_preimage_regularValue hv
          ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v α)) w
        = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
            (f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv
                ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v
              (imagComponent α)) w := by
    intro p _
    have hp_reg : p.val ∈ f.regularSet :=
      f.mem_regularSet_of_preimage_regularValue hv
        ((f.mem_fiberFinset_iff hv p.val).mp p.property)
    have hp_to_v : f.toRiemannSphere p.val = v :=
      (f.mem_fiberFinset_iff hv p.val).mp p.property
    have h_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (f.localSheetData_at_regular hnc hp_reg).g v :=
      mdifferentiableAt_localSheet_g_at_value f hnc hp_reg hp_to_v
    show (imagPartCLM (f.holSheetCotPullback hnc hp_reg v α)) w
      = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
          (f.sheetCotPullback hnc hp_reg v (imagComponent α)) w
    unfold holSheetCotPullback sheetCotPullback
    rw [imagPartCLM_holCotangentPullbackAt_apply h_mdiff α w]
    unfold SmoothPath.applyCotangent
    unfold cotangentPullbackAt
    have h_imagComp :
        (imagComponent α).toFun ((f.localSheetData_at_regular hnc hp_reg).g v)
          = imagPartCLM (α.eval ((f.localSheetData_at_regular hnc hp_reg).g v)) :=
      (imagPartCLM_eval α _).symm
    show Complex.im ((α.eval ((f.localSheetData_at_regular hnc hp_reg).g v))
        ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
          (f.localSheetData_at_regular hnc hp_reg).g v) w))
      = (((imagComponent α).toFun
          ((f.localSheetData_at_regular hnc hp_reg).g v)).comp
            (mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
              (f.localSheetData_at_regular hnc hp_reg).g v)) w
    rw [h_imagComp]
    show Complex.im ((α.eval ((f.localSheetData_at_regular hnc hp_reg).g v))
        ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
          (f.localSheetData_at_regular hnc hp_reg).g v) w))
      = (imagPartCLM (α.eval ((f.localSheetData_at_regular hnc hp_reg).g v)))
          ((mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ))
            (f.localSheetData_at_regular hnc hp_reg).g v) w)
    rw [imagPartCLM_apply]
    rfl
  have general : ∀ (S : Finset { x // x ∈ f.fiberFinset hv })
      (h_each : ∀ p ∈ S,
        (imagPartCLM (f.holSheetCotPullback hnc
          (f.mem_regularSet_of_preimage_regularValue hv
            ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v α)) w
          = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
              (f.sheetCotPullback hnc
                (f.mem_regularSet_of_preimage_regularValue hv
                  ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v
                (imagComponent α)) w),
      (imagPartCLM (∑ p ∈ S, f.holSheetCotPullback hnc
        (f.mem_regularSet_of_preimage_regularValue hv
          ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v α)) w
        = SmoothPath.applyCotangent (I := 𝓘(ℝ, ℂ))
            (∑ p ∈ S, f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hv
                ((f.mem_fiberFinset_iff hv p.val).mp p.property)) v
              (imagComponent α)) w := by
    intro S h_each
    induction S using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, map_zero, ContinuousLinearMap.zero_apply]
        unfold SmoothPath.applyCotangent
        simp only [map_zero, ContinuousLinearMap.zero_apply]
    | insert q s hq ih =>
        rw [Finset.sum_insert hq, Finset.sum_insert hq]
        rw [show
            imagPartCLM (_ + _)
              = imagPartCLM (f.holSheetCotPullback hnc
                  (f.mem_regularSet_of_preimage_regularValue hv
                    ((f.mem_fiberFinset_iff hv q.val).mp q.property)) v α)
                + imagPartCLM (∑ x ∈ s, f.holSheetCotPullback hnc
                    (f.mem_regularSet_of_preimage_regularValue hv
                      ((f.mem_fiberFinset_iff hv x.val).mp x.property)) v α) from
          map_add imagPartCLM _ _]
        rw [ContinuousLinearMap.add_apply]
        unfold SmoothPath.applyCotangent
        rw [show
            SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ)) (_ + _)
              = SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ))
                  (f.sheetCotPullback hnc
                    (f.mem_regularSet_of_preimage_regularValue hv
                      ((f.mem_fiberFinset_iff hv q.val).mp q.property)) v
                    (imagComponent α))
                + SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ))
                    (∑ x ∈ s, f.sheetCotPullback hnc
                      (f.mem_regularSet_of_preimage_regularValue hv
                        ((f.mem_fiberFinset_iff hv x.val).mp x.property)) v
                      (imagComponent α)) from
          map_add (SmoothPath.cotangentEquiv (I := 𝓘(ℝ, ℂ))) _ _]
        rw [ContinuousLinearMap.add_apply]
        rw [h_each q (Finset.mem_insert_self q s)]
        congr 1
        have ih' := ih (fun p hp => h_each p (Finset.mem_insert_of_mem hp))
        unfold SmoothPath.applyCotangent at ih'
        exact ih'
  exact general (f.fiberFinset hv).attach h_per_sheet

end MeromorphicNonzero

end JacobianChallenge

end
