/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothCycleDecompositionToBasedLoops

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Full cycle decomposition: every cycle is in `stokesBoundaries`

**Headline.** Under `BasedSmoothLoopsBoundHypothesis I X p₀`, every
smooth 1-cycle `c : SmoothCycle I X` lies in `stokesBoundaries I X`.

Combined with the unconditional
`basedSmoothLoopsBoundHypothesis_RS_holds`, this gives the explicit
closure `stokesBoundaries 𝓘(ℝ, ℂ) RiemannSphere = ⊤` (the genus-0
input for barrier (2) `H1_spans_top_canonical`).

## Proof sketch

Write `f := c.val : SmoothPath I X →₀ ℤ` (the underlying Finsupp).
The decomposition cycle is

```
ν := ∑ γ ∈ f.support, f γ • singlePlusCorrectionCycle γ
   = ∑ γ, f γ • (single γ + single (α γ.src) - single (α γ.tgt)).
```

Underlying chain: `ν.val = f + S_src - S_tgt`, where
`S_src = ∑ γ, f γ • single (α γ.src)`,
`S_tgt = ∑ γ, f γ • single (α γ.tgt)`. The cycle property
`∂f = 0` (in `X →₀ ℤ`) yields
`∑ γ, f γ • (single γ.tgt - single γ.src) = 0`. The
`αShift : (X →₀ ℤ) →+ SmoothChain I X` sending `single x ↦ single (α x)`
takes this to `S_tgt - S_src = 0`, so `S_src = S_tgt` and
`ν.val = f`. Each summand of `ν` is in `stokesBoundaries` by
`singlePlusCorrectionCycle_mem_stokesBoundaries` (under the
hypothesis), so `ν ∈ stokesBoundaries`, hence `c ∈ stokesBoundaries`.

## What this file ships

* `cycle_in_stokesBoundaries_of_basedLoopsBound`

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

namespace SmoothCycleDecomposition

/-- **Cycle decomposition headline.** Under
`BasedSmoothLoopsBoundHypothesis I X p₀`, every SmoothCycle is in
`stokesBoundaries`. -/
theorem cycle_in_stokesBoundaries_of_basedLoopsBound
    (p₀ : X) (α : X → SmoothPath I X)
    (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)
    (h_loops : BasedSmoothLoopsBoundHypothesis I X p₀)
    (c : SmoothCycle I X) :
    c ∈ stokesBoundaries I X := by
  -- Bind c.val with the explicit Finsupp type so applications work.
  let f : SmoothPath I X →₀ ℤ := c.val
  -- The decomposition cycle.
  let ν : SmoothCycle I X :=
    ∑ γ ∈ f.support,
      f γ • singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
  -- (i) ν ∈ stokesBoundaries.
  have hν_mem : ν ∈ stokesBoundaries I X := by
    apply sum_mem
    intro γ _
    apply AddSubgroup.zsmul_mem
    exact singlePlusCorrectionCycle_mem_stokesBoundaries
      p₀ α h_α_src h_α_tgt h_loops γ
  -- (ii) ν.val = c.val (as SmoothChain, equivalently as Finsupp).
  have hν_chain : (ν : SmoothChain I X) = (c : SmoothChain I X) := by
    show ((∑ γ ∈ f.support, f γ • singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
          : SmoothCycle I X) : SmoothChain I X) = c.val
    rw [AddSubmonoidClass.coe_finset_sum]
    -- Each summand expands at the SmoothChain level.
    have h_summand : ∀ γ : SmoothPath I X,
        ((f γ • singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
            : SmoothCycle I X) : SmoothChain I X)
        = f γ • SmoothChain.single γ
          + f γ • SmoothChain.single (α γ.src)
          - f γ • SmoothChain.single (α γ.tgt) := by
      intro γ
      have h_subtype_zsmul :
          ((f γ • singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
              : SmoothCycle I X) : SmoothChain I X)
            = f γ • ((singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
                : SmoothCycle I X) : SmoothChain I X) := by
        have h := (AddSubgroup.subtype (SmoothCycle I X)).map_zsmul
          (singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ) (f γ)
        exact h
      rw [h_subtype_zsmul]
      rw [singlePlusCorrectionCycle_coe]
      module
    rw [Finset.sum_congr rfl (fun γ _ => h_summand γ)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    -- Sum 1: ∑ γ ∈ f.support, f γ • single γ = f.
    have h_chain_self :
        ∑ γ ∈ f.support, f γ • SmoothChain.single γ = (c.val : SmoothChain I X) := by
      show ∑ γ ∈ f.support, f γ • Finsupp.single γ (1 : ℤ) = c.val
      -- f γ • Finsupp.single γ 1 = Finsupp.single γ (f γ)
      have h_rew : ∀ γ : SmoothPath I X,
          f γ • Finsupp.single γ (1 : ℤ) = Finsupp.single γ (f γ) := by
        intro γ
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl (fun γ _ => h_rew γ)]
      -- ∑ γ ∈ f.support, Finsupp.single γ (f γ) = f.sum Finsupp.single = f
      have : ∑ γ ∈ f.support, Finsupp.single γ (f γ)
          = (f : SmoothPath I X →₀ ℤ).sum Finsupp.single := by
        rw [Finsupp.sum]
      rw [this, Finsupp.sum_single]
    rw [h_chain_self]
    -- Sums 2/3: shifted-by-α sums; equal via cycle property + αShift.
    have h_cycle : SmoothChain.boundary c.val = 0 := SmoothCycle.boundary_toChain c
    let αShift : (X →₀ ℤ) →ₗ[ℤ] SmoothChain I X :=
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
      have h_term : ∀ γ : SmoothPath I X,
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
  have h_eq : ν = c := Subtype.ext hν_chain
  rw [← h_eq]
  exact hν_mem

end SmoothCycleDecomposition

end JacobianChallenge

end
