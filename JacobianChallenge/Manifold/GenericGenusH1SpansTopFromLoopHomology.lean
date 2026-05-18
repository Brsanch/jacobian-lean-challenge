/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycleInStokesBoundariesOfBasedLoopsBound
import JacobianChallenge.Manifold.StokesCanonicalClosedForms

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! # Generic-genus `H1_spans_top` from per-based-loop homology decomposition

For general genus `g = genus X`, the canonical-Stokes-quotient
generation field
`H1_spans_top_canonical : Submodule.span ℤ {S.proj (cycleGens i)} = ⊤`
of `GenericGenusPeriodLatticeInputs` factors through a **per-based-loop
hypothesis**:

> *For every smooth loop `γ` based at `p₀`, `single γ` decomposes as a
> ℤ-linear combination of `cycleGens` modulo `stokesBoundaries`.*

This is the natural genus-≥1 analog of
`BasedSmoothLoopsBoundHypothesis` (the genus-0 hypothesis that every
based loop's `single` lies in `stokesBoundaries` outright — i.e. the
trivial ℤ-combination with all coefficients 0).

When summed over the support of any cycle `c`, the per-loop
decomposition coefficients aggregate into a single tuple of integers
`Nᵢ := ∑_{γ ∈ c.support} c(γ) · nᵢ(γ)` such that

> *`c - ∑ᵢ Nᵢ • cycleGens i ∈ stokesBoundaries`,*

which in the canonical quotient is precisely `S.proj c = ∑ᵢ Nᵢ •
S.proj (cycleGens i)`, hence membership in the ℤ-span. Quantifying
over all `c` gives `H1_spans_top_canonical`.

The proof internally replicates the `αShift` cycle-property
cancellation argument from
`cycle_in_stokesBoundaries_of_basedLoopsBound`, with an extra
ℤ-combination term tracked alongside.

## What this file ships

* `BasedLoopHomologyDecompositionHypothesis` — the per-based-loop
  decomposition predicate (the genuine genus-≥1 hypothesis).
* `H1_spans_top_canonical_of_basedLoopHomology` — the structural
  reduction `BasedLoopHomologyDecompositionHypothesis +
  smooth-path-connectedness ⟹ H1_spans_top_canonical`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-! ## The per-based-loop homology decomposition hypothesis -/

/-- **`BasedLoopHomologyDecompositionHypothesis cycleGens p₀`**.

Says: every smooth loop `γ` based at `p₀` (with both endpoints `p₀`) has
its `single` decomposing as a ℤ-linear combination of `cycleGens` modulo
`stokesBoundaries`.

This is the genuine genus-≥1 analog of `BasedSmoothLoopsBoundHypothesis`
(the genus-0 case is the trivial decomposition with all coefficients
`0`, recovering "single γ ∈ stokesBoundaries"). -/
def BasedLoopHomologyDecompositionHypothesis
    {g : ℕ} (cycleGens : Fin (2 * g) → SmoothCycle 𝓘(ℝ, ℂ) X)
    (p₀ : X) : Prop :=
  ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X, ∀ h_src : γ.src = p₀, ∀ h_tgt : γ.tgt = p₀,
    ∃ n : Fin (2 * g) → ℤ,
      single_smoothLoop_smoothCycle γ (h_src.trans h_tgt.symm)
        - ∑ i, n i • cycleGens i
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X

namespace SmoothCycleDecomposition

variable (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
  (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)

/-- **Per-path decomposition under the per-loop homology hypothesis.**

For any smooth path `γ`, the chain
`single γ + single (α γ.src) - single (α γ.tgt)`
(packaged as `singlePlusCorrectionCycle γ`) differs from a
ℤ-combination of `cycleGens` by an element of `stokesBoundaries`.

This is the per-path version: combining the unconditional rebasing
identity `rebasingCycleOf γ ∈ stokesBoundaries` with the hypothesis
applied to the based loop of `γ` gives:

`singlePlusCorrectionCycle γ ≡ ∑ᵢ nᵢ(γ) • cycleGens i  (mod stokesBoundaries)`

where `nᵢ(γ)` is chosen (classically) per `γ` from the hypothesis. -/
theorem singlePlusCorrectionCycle_eq_zsmul_mod_stokesBoundaries
    {g : ℕ} (cycleGens : Fin (2 * g) → SmoothCycle 𝓘(ℝ, ℂ) X)
    (h_hyp : BasedLoopHomologyDecompositionHypothesis cycleGens p₀)
    (γ : SmoothPath 𝓘(ℝ, ℂ) X) :
    ∃ n : Fin (2 * g) → ℤ,
      singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
        - ∑ i, n i • cycleGens i
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
  -- Apply the hypothesis to the based loop of γ.
  obtain ⟨n, h_basedLoop⟩ :=
    h_hyp (basedLoopOf p₀ α h_α_src h_α_tgt γ)
      (basedLoopOf_src p₀ α h_α_src h_α_tgt γ)
      (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ)
  refine ⟨n, ?_⟩
  -- We have:
  --   (a) rebasingCycleOf γ ∈ stokesBoundaries (unconditional).
  --   (b) single basedLoop - ∑ n_i • cycleGens i ∈ stokesBoundaries (hypothesis).
  -- Sum: single γ + single (α γ.src) - single (α γ.tgt) - ∑ n_i • cycleGens i
  --      ∈ stokesBoundaries.
  have h_rebase :=
    rebasingCycleOf_mem_stokesBoundaries p₀ α h_α_src h_α_tgt γ
  -- Sum (a) and (b).
  have h_sum :
      (rebasingCycleOf p₀ α h_α_src h_α_tgt γ)
        + (single_smoothLoop_smoothCycle
            (basedLoopOf p₀ α h_α_src h_α_tgt γ)
            ((basedLoopOf_src p₀ α h_α_src h_α_tgt γ).trans
              (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ).symm)
          - ∑ i, n i • cycleGens i)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) X :=
    AddSubgroup.add_mem _ h_rebase h_basedLoop
  -- This sum equals singlePlusCorrectionCycle γ - ∑ n_i • cycleGens i.
  have h_eq :
      (rebasingCycleOf p₀ α h_α_src h_α_tgt γ)
        + (single_smoothLoop_smoothCycle
            (basedLoopOf p₀ α h_α_src h_α_tgt γ)
            ((basedLoopOf_src p₀ α h_α_src h_α_tgt γ).trans
              (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ).symm)
          - ∑ i, n i • cycleGens i)
      = singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
        - ∑ i, n i • cycleGens i := by
    apply Subtype.ext
    -- Underlying chain equality.
    rw [SmoothCycle.coe_add, SmoothCycle.coe_sub, SmoothCycle.coe_sub]
    rw [rebasingCycleOf_coe, single_smoothLoop_smoothCycle_coe,
        singlePlusCorrectionCycle_coe]
    abel
  rw [← h_eq]
  exact h_sum

end SmoothCycleDecomposition

/-! ## Headline: `H1_spans_top_canonical` from the per-loop hypothesis -/

/-- **`H1_spans_top_canonical` from `BasedLoopHomologyDecompositionHypothesis`
+ smooth-path-connectedness.**

Under the per-based-loop decomposition hypothesis and a smooth based-path
family `α : X → SmoothPath I X` (smooth-path-connectedness), every
smooth 1-cycle `c` differs from a ℤ-combination of `cycleGens` by a
Stokes-boundary, which in the canonical quotient says
`S.proj c ∈ Submodule.span ℤ {S.proj (cycleGens i)}`. Quantifying over
all `c` gives the headline. -/
theorem H1_spans_top_canonical_of_basedLoopHomology
    {g : ℕ}
    (cycleGens : Fin (2 * g) → SmoothCycle 𝓘(ℝ, ℂ) X)
    (p₀ : X) (α : X → SmoothPath 𝓘(ℝ, ℂ) X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (h_hyp : BasedLoopHomologyDecompositionHypothesis cycleGens p₀) :
    (Submodule.span ℤ
      (Set.range (fun i : Fin (2 * g) =>
        ((StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).proj (cycleGens i) :
          (StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X).H1)))) = ⊤ := by
  -- Abbreviate the canonical bundle.
  set S : StokesBoundaryInvariance 𝓘(ℝ, ℂ) X :=
    StokesBoundaryInvariance.canonical 𝓘(ℝ, ℂ) X with hS_def
  -- It suffices to show every quotient class lies in the span.
  rw [Submodule.eq_top_iff']
  intro hcls
  -- Quotient induction: pick a representative cycle `c` for `hcls`.
  refine QuotientAddGroup.induction_on hcls (fun c => ?_)
  -- For each `γ : SmoothPath`, pick a ℤ-vector `nFn γ` from the
  -- per-path decomposition lemma.
  classical
  let nFn : SmoothPath 𝓘(ℝ, ℂ) X → Fin (2 * g) → ℤ := fun γ =>
    (SmoothCycleDecomposition.singlePlusCorrectionCycle_eq_zsmul_mod_stokesBoundaries
      p₀ α h_α_src h_α_tgt cycleGens h_hyp γ).choose
  have h_nFn :
      ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X,
        SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
            h_α_src h_α_tgt γ
          - ∑ i, nFn γ i • cycleGens i
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := fun γ =>
    (SmoothCycleDecomposition.singlePlusCorrectionCycle_eq_zsmul_mod_stokesBoundaries
      p₀ α h_α_src h_α_tgt cycleGens h_hyp γ).choose_spec
  -- Bind `f := c.val` as a Finsupp.
  let f : SmoothPath 𝓘(ℝ, ℂ) X →₀ ℤ := c.val
  -- The aggregated coefficient tuple: Nᵢ := ∑ γ ∈ f.support, f γ • nFn γ i.
  let N : Fin (2 * g) → ℤ := fun i => ∑ γ ∈ f.support, f γ * nFn γ i
  -- Step 1: aggregate per-path decomposition over c.support.
  -- We claim:  c - ∑ i, N i • cycleGens i  ∈  stokesBoundaries.
  have h_agg :
      c - ∑ i, N i • cycleGens i ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
    -- Sum the per-path memberships, smul'd by f γ.
    have h_sum_terms :
        (∑ γ ∈ f.support,
          f γ • (SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                    h_α_src h_α_tgt γ
                - ∑ i, nFn γ i • cycleGens i))
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) X := by
      apply sum_mem
      intro γ _
      apply AddSubgroup.zsmul_mem
      exact h_nFn γ
    -- Rewrite the summand: distribute smul over the subtraction.
    have h_eq_sum :
        (∑ γ ∈ f.support,
          f γ • (SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                    h_α_src h_α_tgt γ
                - ∑ i, nFn γ i • cycleGens i))
        = (∑ γ ∈ f.support,
            f γ • SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                    h_α_src h_α_tgt γ)
          - (∑ γ ∈ f.support, ∑ i, (f γ * nFn γ i) • cycleGens i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun γ _ => ?_)
      rw [smul_sub]
      congr 1
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul]
    rw [h_eq_sum] at h_sum_terms
    -- Swap the order of summation on the second double sum and identify with
    -- `∑ i, N i • cycleGens i`.
    have h_swap :
        (∑ γ ∈ f.support, ∑ i, (f γ * nFn γ i) • cycleGens i)
          = ∑ i, N i • cycleGens i := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      -- ∑ γ, (f γ * nFn γ i) • cycleGens i = (∑ γ, f γ * nFn γ i) • cycleGens i.
      rw [← Finset.sum_smul]
    rw [h_swap] at h_sum_terms
    -- Now: `∑_γ f γ • singlePlusCorrectionCycle γ - ∑ N_i • cycleGens i ∈ stokesBoundaries`.
    -- Show ∑_γ f γ • singlePlusCorrectionCycle γ = c (this is the αShift
    -- cycle-cancellation argument).
    have h_nu_eq_c :
        (∑ γ ∈ f.support,
          f γ • SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                  h_α_src h_α_tgt γ) = c := by
      apply Subtype.ext
      show ((∑ γ ∈ f.support, f γ •
              SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                h_α_src h_α_tgt γ : SmoothCycle 𝓘(ℝ, ℂ) X) :
            SmoothChain 𝓘(ℝ, ℂ) X) = c.val
      rw [AddSubmonoidClass.coe_finset_sum]
      -- Each summand expands at the SmoothChain level.
      have h_summand : ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X,
          ((f γ • SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
              h_α_src h_α_tgt γ : SmoothCycle 𝓘(ℝ, ℂ) X) :
            SmoothChain 𝓘(ℝ, ℂ) X)
          = f γ • SmoothChain.single γ
            + f γ • SmoothChain.single (α γ.src)
            - f γ • SmoothChain.single (α γ.tgt) := by
        intro γ
        have h_subtype_zsmul :
            ((f γ • SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                h_α_src h_α_tgt γ : SmoothCycle 𝓘(ℝ, ℂ) X) :
              SmoothChain 𝓘(ℝ, ℂ) X)
              = f γ • ((SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
                  h_α_src h_α_tgt γ : SmoothCycle 𝓘(ℝ, ℂ) X) :
                SmoothChain 𝓘(ℝ, ℂ) X) := by
          have h := (AddSubgroup.subtype (SmoothCycle 𝓘(ℝ, ℂ) X)).map_zsmul
            (SmoothCycleDecomposition.singlePlusCorrectionCycle p₀ α
              h_α_src h_α_tgt γ) (f γ)
          exact h
        rw [h_subtype_zsmul]
        rw [SmoothCycleDecomposition.singlePlusCorrectionCycle_coe]
        module
      rw [Finset.sum_congr rfl (fun γ _ => h_summand γ)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      -- Sum 1: ∑ γ ∈ f.support, f γ • single γ = f = c.val.
      have h_chain_self :
          ∑ γ ∈ f.support, f γ • SmoothChain.single γ
            = (c.val : SmoothChain 𝓘(ℝ, ℂ) X) := by
        change ∑ γ ∈ f.support, f γ • Finsupp.single γ (1 : ℤ) = c.val
        have h_rew : ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X,
            f γ • Finsupp.single γ (1 : ℤ) = Finsupp.single γ (f γ) := by
          intro γ
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [Finset.sum_congr rfl (fun γ _ => h_rew γ)]
        have : ∑ γ ∈ f.support, Finsupp.single γ (f γ)
            = (f : SmoothPath 𝓘(ℝ, ℂ) X →₀ ℤ).sum Finsupp.single := by
          rw [Finsupp.sum]
        rw [this, Finsupp.sum_single]
      rw [h_chain_self]
      -- Sums 2/3: shifted-by-α sums; equal via cycle property + αShift.
      have h_cycle : SmoothChain.boundary c.val = 0 :=
        SmoothCycle.boundary_toChain c
      let αShift : (X →₀ ℤ) →ₗ[ℤ] SmoothChain 𝓘(ℝ, ℂ) X :=
        Finsupp.linearCombination ℤ (fun x => SmoothChain.single (α x))
      have h_αShift_single : ∀ (x : X) (a : ℤ),
          αShift (Finsupp.single x a) = a • SmoothChain.single (α x) := by
        intro x a
        change Finsupp.linearCombination ℤ _ (Finsupp.single x a) = _
        rw [Finsupp.linearCombination_single]
        rfl
      have h_shift_bd : αShift (SmoothChain.boundary c.val)
          = ∑ γ ∈ f.support, f γ • SmoothChain.single (α γ.tgt)
            - ∑ γ ∈ f.support, f γ • SmoothChain.single (α γ.src) := by
        have h_bd_expand : SmoothChain.boundary c.val
            = ∑ γ ∈ f.support, f γ • SmoothChain.boundarySingle γ := by
          change Finsupp.linearCombination ℤ SmoothChain.boundarySingle c.val = _
          rw [Finsupp.linearCombination_apply, Finsupp.sum]
        rw [h_bd_expand]
        rw [map_sum]
        have h_term : ∀ γ : SmoothPath 𝓘(ℝ, ℂ) X,
            αShift (f γ • SmoothChain.boundarySingle γ)
              = f γ • SmoothChain.single (α γ.tgt)
                - f γ • SmoothChain.single (α γ.src) := by
          intro γ
          rw [map_zsmul]
          change f γ • αShift (Finsupp.single γ.tgt (1 : ℤ)
                - Finsupp.single γ.src 1) = _
          rw [map_sub]
          rw [h_αShift_single γ.tgt 1, h_αShift_single γ.src 1]
          module
        rw [Finset.sum_congr rfl (fun γ _ => h_term γ)]
        rw [Finset.sum_sub_distrib]
      rw [h_cycle, map_zero] at h_shift_bd
      have h_sums_eq :
          ∑ γ ∈ f.support, f γ • SmoothChain.single (α γ.src)
            = ∑ γ ∈ f.support, f γ • SmoothChain.single (α γ.tgt) :=
        (sub_eq_zero.mp h_shift_bd.symm).symm
      rw [h_sums_eq]
      abel
    rw [h_nu_eq_c] at h_sum_terms
    exact h_sum_terms
  -- Step 2: pass to the canonical quotient.
  -- After `QuotientAddGroup.induction_on`, the goal is
  -- `(QuotientAddGroup.mk c : S.H1) ∈ Submodule.span ℤ ...`,
  -- which is `S.proj c ∈ ...` by definition.
  change S.proj c ∈ Submodule.span ℤ
    (Set.range (fun i : Fin (2 * g) =>
      (S.proj (cycleGens i) : S.H1)))
  -- S.proj (c - ∑ N i • cycleGens i) = 0 → S.proj c = ∑ N i • S.proj (cycleGens i).
  have h_proj_zero :
      S.proj (c - ∑ i, N i • cycleGens i) = (0 : S.H1) := by
    rw [← QuotientAddGroup.eq_zero_iff] at h_agg
    -- `QuotientAddGroup.mk x = S.proj x` definitionally.
    exact h_agg
  have h_proj_sub :
      S.proj (c - ∑ i, N i • cycleGens i)
        = S.proj c - S.proj (∑ i, N i • cycleGens i) :=
    map_sub S.proj _ _
  rw [h_proj_sub] at h_proj_zero
  have h_proj_c_eq :
      S.proj c = S.proj (∑ i, N i • cycleGens i) :=
    sub_eq_zero.mp h_proj_zero
  rw [h_proj_c_eq]
  -- S.proj (∑ N i • cycleGens i) = ∑ N i • S.proj (cycleGens i).
  rw [map_sum]
  -- Each ∑ summand of the form `N i • S.proj (cycleGens i)` lies in the span.
  refine sum_mem (fun i _ => ?_)
  rw [map_zsmul]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

end JacobianChallenge

end
