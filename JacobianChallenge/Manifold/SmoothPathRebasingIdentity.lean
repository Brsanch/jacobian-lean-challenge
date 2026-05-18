/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConcatAdditivityStokes

set_option linter.unusedSectionVars false

/-! # Iterated concat-additivity (rebasing identity precursor)

For three compatible smooth paths `α : SmoothPath I X` (from `p` to `a`),
`γ : SmoothPath I X` (from `a` to `b`), `β.reverse : SmoothPath I X`
(from `b` to `q`), the chain

```
single (α.concat (γ.concat β.reverse h_γβ_rev) h_αγ_outer)
  - single α - single γ - single β.reverse
  ∈ stokesBoundaries I X
```

(when packaged as a SmoothCycle).

Adding two applications of concat-additivity:

* outer: `single (α ⋆ (γ ⋆ β.reverse)) - single α - single (γ ⋆ β.reverse)
    ∈ stokesBoundaries`,
* inner: `single (γ ⋆ β.reverse) - single γ - single β.reverse
    ∈ stokesBoundaries`.

Sum cancels `single (γ ⋆ β.reverse)`:
`single (α ⋆ (γ ⋆ β.reverse)) - single α - single γ - single β.reverse
  ∈ stokesBoundaries`.

## What this file ships

* `triple_concat_chain_mem_smoothCycle` — the chain is a smooth 1-cycle.
* `triple_concat_smoothCycle` — packaged SmoothCycle.
* `triple_concat_in_stokesBoundaries` — the headline membership.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (γ α β : SmoothPath I X)

/-! ## The triple-concat chain is a smooth 1-cycle -/

/-- The chain `single (α ⋆ γ ⋆ β.reverse) - single α - single γ - single β.reverse`
is a smooth 1-cycle. Direct boundary computation: each `single γ_i`
contributes `δ_{tgt_i} - δ_{src_i}`, and the cancellation of net
endpoints follows from `α.tgt = γ.src` and `γ.tgt = β.reverse.src
= β.tgt`. -/
lemma triple_concat_chain_mem_smoothCycle
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src) :
    SmoothChain.single
        (α.concat (γ.concat β.reverse h_γβ_rev)
          (by rw [SmoothPath.concat_src]; exact h_αγ))
      - SmoothChain.single α
      - SmoothChain.single γ
      - SmoothChain.single β.reverse
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single
          (α.concat (γ.concat β.reverse h_γβ_rev)
            (by rw [SmoothPath.concat_src]; exact h_αγ))
        - SmoothChain.single α - SmoothChain.single γ
        - SmoothChain.single β.reverse
        = SmoothChain.single
            (α.concat (γ.concat β.reverse h_γβ_rev)
              (by rw [SmoothPath.concat_src]; exact h_αγ))
          + (-SmoothChain.single α)
          + (-SmoothChain.single γ)
          + (-SmoothChain.single β.reverse) from by abel]
  rw [SmoothCycle.mem_iff,
      SmoothChain.boundary_add, SmoothChain.boundary_add, SmoothChain.boundary_add,
      SmoothChain.boundary_neg, SmoothChain.boundary_neg, SmoothChain.boundary_neg,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle]
  simp [SmoothPath.concat_src, SmoothPath.concat_tgt, SmoothPath.reverse_src,
    SmoothPath.reverse_tgt, h_αγ, h_γβ_rev]

/-- The packaged triple-concat SmoothCycle. -/
noncomputable def triple_concat_smoothCycle
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src) :
    SmoothCycle I X :=
  ⟨SmoothChain.single
      (α.concat (γ.concat β.reverse h_γβ_rev)
        (by rw [SmoothPath.concat_src]; exact h_αγ))
    - SmoothChain.single α
    - SmoothChain.single γ
    - SmoothChain.single β.reverse,
    triple_concat_chain_mem_smoothCycle γ α β h_αγ h_γβ_rev⟩

@[simp] lemma triple_concat_smoothCycle_coe
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src) :
    (triple_concat_smoothCycle γ α β h_αγ h_γβ_rev : SmoothChain I X)
      = SmoothChain.single
          (α.concat (γ.concat β.reverse h_γβ_rev)
            (by rw [SmoothPath.concat_src]; exact h_αγ))
        - SmoothChain.single α
        - SmoothChain.single γ
        - SmoothChain.single β.reverse := rfl

/-! ## Headline: iterated concat-additivity -/

/-- Chain-level cancellation: the sum of the outer + inner
concat-additive chains equals the triple-concat chain. -/
private lemma triple_concat_chain_collapse
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src) :
    (SmoothChain.single
        (α.concat (γ.concat β.reverse h_γβ_rev)
          (by rw [SmoothPath.concat_src]; exact h_αγ))
        - SmoothChain.single α
        - SmoothChain.single (γ.concat β.reverse h_γβ_rev))
      + (SmoothChain.single (γ.concat β.reverse h_γβ_rev)
        - SmoothChain.single γ
        - SmoothChain.single β.reverse)
      = SmoothChain.single
          (α.concat (γ.concat β.reverse h_γβ_rev)
            (by rw [SmoothPath.concat_src]; exact h_αγ))
        - SmoothChain.single α
        - SmoothChain.single γ
        - SmoothChain.single β.reverse := by
  abel

/-- **Iterated concat-additivity (triple concat).**

For smooth paths `α, γ, β : SmoothPath I X` with `α.tgt = γ.src` and
`γ.tgt = β.reverse.src` (i.e., `γ.tgt = β.tgt` via reverse), the chain
`single (α ⋆ γ ⋆ β.reverse) - single α - single γ - single β.reverse`
(packaged as a SmoothCycle) lies in `stokesBoundaries I X`. -/
theorem triple_concat_in_stokesBoundaries
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src) :
    triple_concat_smoothCycle γ α β h_αγ h_γβ_rev
      ∈ stokesBoundaries I X := by
  -- Construct h_αγ_outer : α.tgt = (γ.concat β.reverse h_γβ_rev).src.
  have h_αγ_outer : α.tgt = (γ.concat β.reverse h_γβ_rev).src := by
    rw [SmoothPath.concat_src]; exact h_αγ
  -- Pull in the two concat-additivity memberships.
  have h_outer :=
    concat_additive_in_stokesBoundaries
      (I := I) (X := X) α (γ.concat β.reverse h_γβ_rev) h_αγ_outer
  have h_inner :=
    concat_additive_in_stokesBoundaries
      (I := I) (X := X) γ β.reverse h_γβ_rev
  have h_sum :
      concat_additive_smoothCycle α (γ.concat β.reverse h_γβ_rev) h_αγ_outer
        + concat_additive_smoothCycle γ β.reverse h_γβ_rev
        ∈ stokesBoundaries I X :=
    AddSubgroup.add_mem _ h_outer h_inner
  -- Show this equals triple_concat_smoothCycle γ α β h_αγ h_γβ_rev.
  have h_eq :
      concat_additive_smoothCycle α (γ.concat β.reverse h_γβ_rev) h_αγ_outer
        + concat_additive_smoothCycle γ β.reverse h_γβ_rev
      = triple_concat_smoothCycle γ α β h_αγ h_γβ_rev := by
    apply Subtype.ext
    rw [SmoothCycle.coe_add]
    rw [concat_additive_smoothCycle_coe, concat_additive_smoothCycle_coe,
        triple_concat_smoothCycle_coe]
    exact triple_concat_chain_collapse γ α β h_αγ h_γβ_rev
  rw [← h_eq]
  exact h_sum

end JacobianChallenge

end
