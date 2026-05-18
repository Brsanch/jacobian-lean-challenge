/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathRebasingFull
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-! # Cycle decomposition: basedLoopOf primitive

Given a smooth manifold `X`, a chosen basepoint `p₀ : X`, and a function
`α : X → SmoothPath I X` providing smooth based paths
(`(α x).src = p₀`, `(α x).tgt = x`), defines the based loop associated
to any smooth path `γ`:

```
basedLoopOf γ := α(γ.src) ⋆ γ ⋆ (α γ.tgt).reverse : SmoothPath I X.
```

Both endpoints are `p₀`. The full cycle-decomposition theorem (every
smooth 1-cycle reduces to a sum of based loops mod stokesBoundaries)
builds on this primitive.

## What this file ships

* `basedLoopOf α γ` — the based loop construction.
* `basedLoopOf_src`, `basedLoopOf_tgt` — endpoint identities.
* `rebasingChainOf_mem_smoothCycle` — the rebasing chain is a SmoothCycle.
* `rebasingCycleOf` — packaged.
* `rebasingCycleOf_mem_stokesBoundaries` — discharged via existing
  `rebasing_in_stokesBoundaries`.

The full decomposition headline
`cycle_in_stokesBoundaries_of_basedLoopsBound` requires further
Finsupp.sum machinery (rebasing-correction-collapses-for-cycles); that
remains as a follow-up chip.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

namespace SmoothCycleDecomposition

variable (p₀ : X) (α : X → SmoothPath I X)
  (h_α_src : ∀ x, (α x).src = p₀) (h_α_tgt : ∀ x, (α x).tgt = x)

include h_α_src h_α_tgt

/-- The based loop associated to a smooth path `γ`. -/
noncomputable def basedLoopOf (γ : SmoothPath I X) : SmoothPath I X :=
  have _h_src_used := h_α_src
  have h_γ_α_tgt_rev : γ.tgt = (α γ.tgt).reverse.src := by
    rw [SmoothPath.reverse_src, h_α_tgt]
  have h_α_src_γ : (α γ.src).tgt
      = (γ.concat (α γ.tgt).reverse h_γ_α_tgt_rev).src := by
    rw [SmoothPath.concat_src, h_α_tgt]
  (α γ.src).concat (γ.concat (α γ.tgt).reverse h_γ_α_tgt_rev) h_α_src_γ

lemma basedLoopOf_src (γ : SmoothPath I X) :
    (basedLoopOf p₀ α h_α_src h_α_tgt γ).src = p₀ := by
  show (α γ.src).src = p₀
  exact h_α_src γ.src

lemma basedLoopOf_tgt (γ : SmoothPath I X) :
    (basedLoopOf p₀ α h_α_src h_α_tgt γ).tgt = p₀ := by
  show (α γ.tgt).src = p₀
  exact h_α_src γ.tgt

/-! ## Rebasing per path -/

/-- For each smooth path `γ`, the rebasing chain
`single γ - single (basedLoopOf γ) + single (α γ.src) - single (α γ.tgt)`
is a smooth 1-cycle. -/
lemma rebasingChainOf_mem_smoothCycle (γ : SmoothPath I X) :
    SmoothChain.single γ
      - SmoothChain.single (basedLoopOf p₀ α h_α_src h_α_tgt γ)
      + SmoothChain.single (α γ.src)
      - SmoothChain.single (α γ.tgt)
      ∈ JacobianChallenge.SmoothCycle I X := by
  have h_αγ : (α γ.src).tgt = γ.src := h_α_tgt γ.src
  have h_γβ_rev : γ.tgt = (α γ.tgt).reverse.src := by
    rw [SmoothPath.reverse_src, h_α_tgt]
  have hα_src : (α γ.src).src = (α γ.tgt).src := by
    rw [h_α_src, h_α_src]
  exact rebasing_chain_mem_smoothCycle γ (α γ.src) (α γ.tgt) h_αγ h_γβ_rev hα_src

/-- Packaged rebasing SmoothCycle for γ. -/
noncomputable def rebasingCycleOf (γ : SmoothPath I X) : SmoothCycle I X :=
  ⟨SmoothChain.single γ
    - SmoothChain.single (basedLoopOf p₀ α h_α_src h_α_tgt γ)
    + SmoothChain.single (α γ.src)
    - SmoothChain.single (α γ.tgt),
    rebasingChainOf_mem_smoothCycle p₀ α h_α_src h_α_tgt γ⟩

@[simp] lemma rebasingCycleOf_coe (γ : SmoothPath I X) :
    (rebasingCycleOf p₀ α h_α_src h_α_tgt γ : SmoothChain I X)
      = SmoothChain.single γ
        - SmoothChain.single (basedLoopOf p₀ α h_α_src h_α_tgt γ)
        + SmoothChain.single (α γ.src)
        - SmoothChain.single (α γ.tgt) := rfl

lemma rebasingCycleOf_mem_stokesBoundaries (γ : SmoothPath I X) :
    rebasingCycleOf p₀ α h_α_src h_α_tgt γ ∈ stokesBoundaries I X := by
  have h_αγ : (α γ.src).tgt = γ.src := h_α_tgt γ.src
  have h_γβ_rev : γ.tgt = (α γ.tgt).reverse.src := by
    rw [SmoothPath.reverse_src, h_α_tgt]
  have hα_src : (α γ.src).src = (α γ.tgt).src := by
    rw [h_α_src, h_α_src]
  have h_rebase :=
    rebasing_in_stokesBoundaries γ (α γ.src) (α γ.tgt) h_αγ h_γβ_rev hα_src
  have h_eq : rebasingCycleOf p₀ α h_α_src h_α_tgt γ
      = rebasing_smoothCycle γ (α γ.src) (α γ.tgt) h_αγ h_γβ_rev hα_src := by
    apply Subtype.ext
    rw [rebasingCycleOf_coe, rebasing_smoothCycle_coe]
    rfl
  rw [h_eq]
  exact h_rebase

/-! ## Per-path discharge: `single γ + (correction) ∈ stokesBoundaries`

Combining `rebasingCycleOf γ ∈ stokesBoundaries` with the
based-loop-bound hypothesis gives that

```
single γ + single (α γ.src) - single (α γ.tgt) ∈ stokesBoundaries
```

(as a SmoothCycle). Note this still has the "correction" term `single
α(γ.src) - single α(γ.tgt)`; when summed over a cycle, the correction
cancels. -/

/-- The chain `single γ + single (α γ.src) - single (α γ.tgt)` is a
SmoothCycle (the boundary computes to 0). -/
lemma single_plus_correction_mem_smoothCycle (γ : SmoothPath I X) :
    SmoothChain.single γ
      + SmoothChain.single (α γ.src)
      - SmoothChain.single (α γ.tgt)
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single γ
        + SmoothChain.single (α γ.src)
        - SmoothChain.single (α γ.tgt)
      = SmoothChain.single γ
        + SmoothChain.single (α γ.src)
        + (-SmoothChain.single (α γ.tgt)) from by abel]
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_add, SmoothChain.boundary_add,
      SmoothChain.boundary_neg, SmoothChain.boundary_single,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle,
      SmoothChain.boundarySingle]
  simp [h_α_src, h_α_tgt]

/-- Packaged SmoothCycle. -/
noncomputable def singlePlusCorrectionCycle (γ : SmoothPath I X) :
    SmoothCycle I X :=
  ⟨SmoothChain.single γ
    + SmoothChain.single (α γ.src)
    - SmoothChain.single (α γ.tgt),
    single_plus_correction_mem_smoothCycle p₀ α h_α_src h_α_tgt γ⟩

@[simp] lemma singlePlusCorrectionCycle_coe (γ : SmoothPath I X) :
    (singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ : SmoothChain I X)
      = SmoothChain.single γ
        + SmoothChain.single (α γ.src)
        - SmoothChain.single (α γ.tgt) := rfl

/-- **Per-path discharge.** If `single (basedLoopOf γ)` is in
stokesBoundaries (as a SmoothCycle), then so is
`single γ + single (α γ.src) - single (α γ.tgt)`. -/
theorem singlePlusCorrectionCycle_mem_stokesBoundaries
    (h_loops : BasedSmoothLoopsBoundHypothesis I X p₀)
    (γ : SmoothPath I X) :
    singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ
      ∈ stokesBoundaries I X := by
  -- single γ + single (α γ.src) - single (α γ.tgt)
  --   = (single γ - single (basedLoopOf γ) + single (α γ.src) - single (α γ.tgt))
  --     + single (basedLoopOf γ)
  --   = rebasingCycleOf γ + single_smoothLoop_smoothCycle (basedLoopOf γ).
  -- Both summands are in stokesBoundaries.
  have h_rebase :=
    rebasingCycleOf_mem_stokesBoundaries p₀ α h_α_src h_α_tgt γ
  have h_basedLoop_in : single_smoothLoop_smoothCycle
        (basedLoopOf p₀ α h_α_src h_α_tgt γ)
        ((basedLoopOf_src p₀ α h_α_src h_α_tgt γ).trans
          (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ).symm)
      ∈ stokesBoundaries I X :=
    h_loops _ (basedLoopOf_src p₀ α h_α_src h_α_tgt γ)
      (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ)
  -- Sum the two.
  have h_sum :
      rebasingCycleOf p₀ α h_α_src h_α_tgt γ +
        single_smoothLoop_smoothCycle
          (basedLoopOf p₀ α h_α_src h_α_tgt γ)
          ((basedLoopOf_src p₀ α h_α_src h_α_tgt γ).trans
            (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ).symm)
      ∈ stokesBoundaries I X :=
    AddSubgroup.add_mem _ h_rebase h_basedLoop_in
  -- Show this equals singlePlusCorrectionCycle γ at the cycle level.
  have h_eq :
      rebasingCycleOf p₀ α h_α_src h_α_tgt γ +
        single_smoothLoop_smoothCycle
          (basedLoopOf p₀ α h_α_src h_α_tgt γ)
          ((basedLoopOf_src p₀ α h_α_src h_α_tgt γ).trans
            (basedLoopOf_tgt p₀ α h_α_src h_α_tgt γ).symm)
      = singlePlusCorrectionCycle p₀ α h_α_src h_α_tgt γ := by
    apply Subtype.ext
    rw [SmoothCycle.coe_add]
    rw [rebasingCycleOf_coe, single_smoothLoop_smoothCycle_coe,
        singlePlusCorrectionCycle_coe]
    abel
  rw [← h_eq]
  exact h_sum

end SmoothCycleDecomposition

end JacobianChallenge

end
