/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusLiftedOrderCorrespondence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! # Regular points of the lifted elliptic function

Pre-assembly glue for piece 5 of the forward-Abel contour argument
(`HANDOFF_TLDIVSUM.md`): at a point where the meromorphic order is `0`
and the function is continuous, the function is **honestly analytic
and nonvanishing** — including the value at the point itself
(`analyticAt_nonzero_of_meromorphicOrderAt_eq_zero`; the continuity
hypothesis pins the pointwise value to the germ limit).

Applied to the lifted elliptic function: at every `z` whose class has
`mmeromorphicOrderAt f (mkQ z) = 0` (i.e. off the divisor support),
`liftedFun L f` is analytic and nonvanishing at `z`
(`liftedFun_analyticAt_nonzero_of_order_zero`) — exactly the
regularity input `hreg` of `abelIntegrand_decomposition` and the
side-regularity inputs of `boundaryIntegral_mul_logDeriv_mem`.

No `sorry`, no `axiom`. -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace JacobianChallenge

/-- **Order zero + continuity ⟹ analytic nonvanishing.** A function
meromorphic at `z` of meromorphic order `0` that is continuous at `z`
is analytic at `z` with nonzero value: the order-`0` normal form gives
an analytic nonvanishing `G` agreeing with `F` on a punctured
neighborhood, and continuity forces `F z = G z`. -/
theorem analyticAt_nonzero_of_meromorphicOrderAt_eq_zero
    {F : ℂ → ℂ} {z : ℂ}
    (hF : MeromorphicAt F z)
    (h0 : meromorphicOrderAt F z = 0)
    (hcont : ContinuousAt F z) :
    AnalyticAt ℂ F z ∧ F z ≠ 0 := by
  obtain ⟨G, hG, hGz, hev⟩ := (meromorphicOrderAt_eq_int_iff hF
    (n := 0)).mp (by exact_mod_cast h0)
  have hev' : F =ᶠ[𝓝[≠] z] G := by
    filter_upwards [hev] with w hw
    simpa using hw
  -- The pointwise value agrees with the germ limit.
  have hFz : F z = G z := by
    haveI : (𝓝[≠] z).NeBot := inferInstance
    have h1 : Filter.Tendsto F (𝓝[≠] z) (𝓝 (F z)) :=
      hcont.continuousWithinAt.tendsto
    have h2 : Filter.Tendsto F (𝓝[≠] z) (𝓝 (G z)) := by
      apply Filter.Tendsto.congr' hev'.symm
      exact hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique h1 h2
  -- Upgrade the punctured agreement to a full neighborhood.
  have hfull : F =ᶠ[𝓝 z] G := by
    have h3 := eventually_nhdsWithin_iff.mp hev'
    filter_upwards [h3] with w hw
    by_cases hwz : w = z
    · subst hwz
      exact hFz
    · exact hw (Set.mem_compl_singleton_iff.mpr hwz)
  refine ⟨hG.congr hfull.symm, ?_⟩
  rw [hFz]
  exact hGz

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Regular points of the lift**: at every `z` whose class carries
meromorphic order `0`, the lifted elliptic function is analytic and
nonvanishing. This is the regularity input of the piece-5 assembly
(`hreg` of `abelIntegrand_decomposition`, side conditions of
`boundaryIntegral_mul_logDeriv_mem`). -/
theorem liftedFun_analyticAt_nonzero_of_order_zero
    (f : MeromorphicNonzero (ℂ ⧸ L)) {z : ℂ}
    (h0 : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun (L.mkQ z) = 0) :
    AnalyticAt ℂ (liftedFun L f) z ∧ liftedFun L f z ≠ 0 := by
  -- The lifted order at `z` is zero by the order correspondence.
  have hord : meromorphicOrderAt (liftedFun L f) z = 0 := by
    rw [liftedOrderCorrespondence_holds L f z, h0]
  -- The lift is meromorphic at `z`.
  have hF : MeromorphicAt (liftedFun L f) z := meromorphic_liftedFun L f z
  -- The lift is continuous at `z`: `f` is continuous at the non-pole
  -- class point, and the quotient map is continuous.
  have hcont : ContinuousAt (liftedFun L f) z := by
    have hf_cont : ContinuousAt f.toFun (L.mkQ z) :=
      f.regular_continuousAt (L.mkQ z) (le_of_eq h0.symm)
    have hmkQ : Continuous (L.mkQ : ℂ → ℂ ⧸ L) :=
      (L.isOpenQuotientMap_mkQ).continuous
    exact ContinuousAt.comp (g := f.toFun)
      (f := (L.mkQ : ℂ → ℂ ⧸ L)) hf_cont hmkQ.continuousAt
  exact analyticAt_nonzero_of_meromorphicOrderAt_eq_zero hF hord hcont

end ComplexTorus

end JacobianChallenge

end
