/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SourceSheetSumEqTraceAt
import JacobianChallenge.Manifold.PerFiberSheetEventually

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Eventually-form of the per-`t` trace identity

Composes:
* `eventually_forall_betaSigma_in_sheetV` (sub-interval condition holds
  eventually for all fibre points),
* `eventually_forall_sheet_lift_eq` (lift-equality holds eventually for
  all fibre points),
* eventually `β(σ t) ∈ regularValueSet` (from openness +
  `β(σ 0) = β 0 ∈ regularValueSet`),
* `source_sheet_sum_eq_traceAt`.

Headline: for `t` in a right-neighbourhood of `0`, the source-side
sheet cotangent pullback sum equals `traceAt f hnc hβσt_reg ω`, where
`hβσt_reg` is the eventually-discharged regular-value membership.

The eventually formulation is the natural input to the Lebesgue
subdivision step: on each piece of the Hurwitz partition of `[0, 1]`,
the same machinery applies (with a shifted base point) and the trace
identity holds. The composed integral statement is then derivable by
piecewise integration.

## What ships

* `MeromorphicNonzero.eventually_source_sheet_sum_eq_traceAt` — the
  eventually-form headline.

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

/-- **Eventually-form of `source_sheet_sum_eq_traceAt`.**

For `t` in a right-neighbourhood of `0`, the source-side sheet
cotangent pullback sum equals `traceAt f hnc hβσt_reg ω`. The
hypotheses `h_sub_interval`, `h_lift_eq`, and `β(σ t) ∈ regularValueSet`
are all discharged on a common right-neighbourhood of `0`. -/
theorem eventually_source_sheet_sum_eq_traceAt
    (f : MeromorphicNonzero X)
    (hnc : ¬ JacobianChallenge.IsConstantMap f.toRiemannSphere)
    {β : ℝ → RiemannSphere}
    (hβ_smooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β)
    (hβ_reg : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ f.regularValueSet)
    (om : SmoothOneForm 𝓘(ℝ, ℂ) X)
    (hβ0_reg : β 0 ∈ f.regularValueSet) :
    ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] (0 : ℝ),
      ∃ hβσt_reg : β (Real.smoothTransition t) ∈ f.regularValueSet,
        ∑ p ∈ (f.sourceFiber hβ0_reg).attach,
            f.sheetCotPullback hnc
              (f.mem_regularSet_of_preimage_regularValue hβ0_reg
                ((f.mem_sourceFiber_iff hβ0_reg p.val).mp p.property))
              (β (Real.smoothTransition t)) om
          = f.traceAt hnc hβσt_reg om := by
  classical
  -- Build the eventually-set: intersect 𝓝[Icc 0 1] 0 with the three eventually-conditions.
  -- 1. β(σ t) ∈ regularValueSet eventually (in 𝓝 0).
  have h_reg_eventually : ∀ᶠ t in 𝓝 (0 : ℝ),
      β (Real.smoothTransition t) ∈ f.regularValueSet := by
    have hβσ_cont : Continuous (fun t : ℝ => β (Real.smoothTransition t)) :=
      hβ_smooth.continuous.comp Real.smoothTransition.continuous
    have h0_in : (0 : ℝ) ∈ (fun t : ℝ => β (Real.smoothTransition t))
        ⁻¹' f.regularValueSet := by
      simp only [Set.mem_preimage, Real.smoothTransition.zero]; exact hβ0_reg
    exact (hβσ_cont.isOpen_preimage _ (f.regularValueSet_isOpen hnc)).mem_nhds h0_in
  -- 2. β(σ t) ∈ sheet_p.V for all p ∈ sourceFiber (in 𝓝 0).
  have h_sub_eventually := f.eventually_forall_betaSigma_in_sheetV hnc hβ_smooth hβ_reg
  -- 3. lift-eq for all p (in 𝓝[≥] 0).
  have h_lift_eventually := f.eventually_forall_sheet_lift_eq hnc hβ_smooth hβ_reg
  -- We work in 𝓝[Icc 0 1] 0, which is sandwiched between 𝓝[≥] 0 and 𝓝 0.
  -- The 𝓝[≥] 0 filter membership transfers to 𝓝[Icc 0 1] 0 via the inclusion
  -- Icc 0 1 ⊆ {t | 0 ≤ t}.
  have h_Icc_le_Ici : 𝓝[Icc (0:ℝ) 1] (0 : ℝ) ≤ 𝓝[≥] (0 : ℝ) :=
    nhdsWithin_mono _ Icc_subset_Ici_self
  have h_Icc_le_nhds : 𝓝[Icc (0:ℝ) 1] (0 : ℝ) ≤ 𝓝 (0 : ℝ) :=
    nhdsWithin_le_nhds
  -- Replicate the conditions in the smaller filter.
  have h_reg_Icc : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (0 : ℝ),
      β (Real.smoothTransition t) ∈ f.regularValueSet :=
    h_Icc_le_nhds h_reg_eventually
  have h_sub_Icc : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (0 : ℝ),
      ∀ p : { x // x ∈ f.sourceFiber
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
        β (Real.smoothTransition t) ∈
          (f.localSheetData_at_regular hnc
            (f.mem_regularSet_of_preimage_regularValue
              (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
              ((f.mem_sourceFiber_iff
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).V :=
    h_Icc_le_nhds h_sub_eventually
  have h_lift_Icc : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (0 : ℝ),
      ∀ p : { x // x ∈ f.sourceFiber
          (hβ_reg 0 ⟨le_refl _, by norm_num⟩) },
        (f.sourceFiberPath hnc hβ_smooth hβ_reg
          ((f.mem_sourceFiber_iff
            (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property)).toPath.extend t
          = (f.localSheetData_at_regular hnc
              (f.mem_regularSet_of_preimage_regularValue
                (hβ_reg 0 ⟨le_refl _, by norm_num⟩)
                ((f.mem_sourceFiber_iff
                  (hβ_reg 0 ⟨le_refl _, by norm_num⟩) p.val).mp p.property))).g
              (β (Real.smoothTransition t)) :=
    h_Icc_le_Ici h_lift_eventually
  have h_self_Icc : ∀ᶠ t in 𝓝[Icc (0:ℝ) 1] (0 : ℝ),
      t ∈ Icc (0 : ℝ) 1 := self_mem_nhdsWithin
  -- Combine and apply source_sheet_sum_eq_traceAt.
  filter_upwards [h_reg_Icc, h_sub_Icc, h_lift_Icc, h_self_Icc] with
    t h_reg_t h_sub_t h_lift_t h_self_t
  -- The hβ0_reg in the conclusion type comes from the user-provided arg,
  -- but the `h_sub_t` and `h_lift_t` use the chip's internal one.
  -- They're propositionally equal, so a `Subsingleton.elim`-like rewrite works.
  have h_chip_hβ0_eq : (hβ_reg 0 ⟨le_refl _, by norm_num⟩) = hβ0_reg := rfl
  refine ⟨h_reg_t, ?_⟩
  exact f.source_sheet_sum_eq_traceAt hnc hβ_smooth hβ_reg om h_self_t h_reg_t hβ0_reg
    h_sub_t h_lift_t

end MeromorphicNonzero

end JacobianChallenge

end
