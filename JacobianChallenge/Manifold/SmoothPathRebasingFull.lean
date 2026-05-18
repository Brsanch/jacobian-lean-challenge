/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathRebasingIdentity

set_option linter.unusedSectionVars false

/-! # Full rebasing identity in stokesBoundaries

**Headline.** For a smooth path `γ : a → b` and any smooth based paths
`α : p₀ → a`, `β : p₀ → b`, the chain

```
single γ - single (α ⋆ γ ⋆ β.reverse) + single α - single β
  ∈ stokesBoundaries I X.
```

(Packaged as a SmoothCycle.) Equivalently:

```
single γ ≡ single (α ⋆ γ ⋆ β.reverse) - single α + single β
                                         (mod stokesBoundaries).
```

This is the **rebasing identity proper**: every smooth path γ : a → b
is homologous (mod stokes-boundaries) to a based loop `ℓ` at the
basepoint `p₀`, MINUS the auxiliary "rebasing corrections"
`single α - single β` involving the chosen based paths.

When summed over a smooth 1-cycle `c = ∑ aᵢ γᵢ`, the rebasing
corrections collapse: the cycle property `∂c = 0` together with a
canonical choice `α(x) : p₀ → x` per point `x` makes the
`single β - single α` contributions for each individual γᵢ assemble
into `∑_x m(x) * single α(x)` where `m(x)` is the boundary multiplicity
of `x` in `c`. Since `c` is a cycle, `m(x) = 0` everywhere, so the
rebasing corrections vanish entirely, and `c` reduces (mod
stokes-boundaries) to a `ℤ`-linear sum of based loops at `p₀`.

## Proof

Combines:

* `triple_concat_in_stokesBoundaries`:
  `single (α ⋆ γ ⋆ β.reverse) - single α - single γ - single β.reverse
    ∈ stokesBoundaries`.
* Path-plus-reverse identity for `β`:
  `single β + single β.reverse ∈ stokesBoundaries`.

Negating the first and adding the second:

```
- (single (α ⋆ γ ⋆ β.reverse) - single α - single γ - single β.reverse)
  - (single β + single β.reverse)
= - single (α ⋆ γ ⋆ β.reverse) + single α + single γ + single β.reverse
    - single β - single β.reverse
= single γ - single (α ⋆ γ ⋆ β.reverse) + single α - single β.
```

So this chain lies in `stokesBoundaries`.

## What this file ships

* `rebasing_chain_mem_smoothCycle` — chain is a smooth 1-cycle.
* `rebasing_smoothCycle` — packaged SmoothCycle.
* `rebasing_in_stokesBoundaries` — the headline membership.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (γ α β : SmoothPath I X)

/-! ## The rebasing chain is a smooth 1-cycle -/

/-- The chain
`single γ - single (α ⋆ γ ⋆ β.reverse) + single α - single β`
is a smooth 1-cycle. Boundary computation: contributions from each
single cancel out. -/
lemma rebasing_chain_mem_smoothCycle
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src)
    (hα_src : α.src = β.src) :
    SmoothChain.single γ
      - SmoothChain.single
          (α.concat (γ.concat β.reverse h_γβ_rev)
            (by rw [SmoothPath.concat_src]; exact h_αγ))
      + SmoothChain.single α
      - SmoothChain.single β
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single γ
        - SmoothChain.single
            (α.concat (γ.concat β.reverse h_γβ_rev)
              (by rw [SmoothPath.concat_src]; exact h_αγ))
        + SmoothChain.single α
        - SmoothChain.single β
      = SmoothChain.single γ
        + (-SmoothChain.single
            (α.concat (γ.concat β.reverse h_γβ_rev)
              (by rw [SmoothPath.concat_src]; exact h_αγ)))
        + SmoothChain.single α
        + (-SmoothChain.single β) from by abel]
  rw [SmoothCycle.mem_iff,
      SmoothChain.boundary_add, SmoothChain.boundary_add, SmoothChain.boundary_add,
      SmoothChain.boundary_neg, SmoothChain.boundary_neg,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle]
  -- α.src = β.src = p₀; α.tgt = γ.src = a; γ.tgt = β.reverse.src = β.tgt = b.
  -- Compute β.reverse.src = β.tgt and the outer concat endpoints.
  simp [SmoothPath.concat_src, SmoothPath.concat_tgt, SmoothPath.reverse_src,
    SmoothPath.reverse_tgt, h_αγ, h_γβ_rev, hα_src]

/-- Packaged rebasing SmoothCycle. -/
noncomputable def rebasing_smoothCycle
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src)
    (hα_src : α.src = β.src) : SmoothCycle I X :=
  ⟨SmoothChain.single γ
      - SmoothChain.single
          (α.concat (γ.concat β.reverse h_γβ_rev)
            (by rw [SmoothPath.concat_src]; exact h_αγ))
      + SmoothChain.single α
      - SmoothChain.single β,
    rebasing_chain_mem_smoothCycle γ α β h_αγ h_γβ_rev hα_src⟩

@[simp] lemma rebasing_smoothCycle_coe
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src)
    (hα_src : α.src = β.src) :
    (rebasing_smoothCycle γ α β h_αγ h_γβ_rev hα_src : SmoothChain I X)
      = SmoothChain.single γ
        - SmoothChain.single
            (α.concat (γ.concat β.reverse h_γβ_rev)
              (by rw [SmoothPath.concat_src]; exact h_αγ))
        + SmoothChain.single α
        - SmoothChain.single β := rfl

/-! ## Chain-level cancellation -/

private lemma rebasing_chain_collapse
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src) :
    - (SmoothChain.single
          (α.concat (γ.concat β.reverse h_γβ_rev)
            (by rw [SmoothPath.concat_src]; exact h_αγ))
        - SmoothChain.single α
        - SmoothChain.single γ
        - SmoothChain.single β.reverse)
      - (SmoothChain.single β + SmoothChain.single β.reverse)
      = SmoothChain.single γ
        - SmoothChain.single
            (α.concat (γ.concat β.reverse h_γβ_rev)
              (by rw [SmoothPath.concat_src]; exact h_αγ))
        + SmoothChain.single α
        - SmoothChain.single β := by
  abel

/-! ## Headline -/

/-- **Rebasing identity for a single smooth path.**

For a smooth path `γ : a → b` and any smooth based paths
`α : p₀ → a`, `β : p₀ → b`, the chain

```
single γ - single (α ⋆ γ ⋆ β.reverse) + single α - single β
```

(packaged as a SmoothCycle) lies in `stokesBoundaries I X`.

Equivalently: `[γ] = [α ⋆ γ ⋆ β.reverse] - [α] + [β]` in the canonical
Stokes H₁ quotient. -/
theorem rebasing_in_stokesBoundaries
    (h_αγ : α.tgt = γ.src) (h_γβ_rev : γ.tgt = β.reverse.src)
    (hα_src : α.src = β.src) :
    rebasing_smoothCycle γ α β h_αγ h_γβ_rev hα_src
      ∈ stokesBoundaries I X := by
  have h_triple :=
    triple_concat_in_stokesBoundaries (I := I) (X := X) γ α β h_αγ h_γβ_rev
  have h_neg_triple := AddSubgroup.neg_mem _ h_triple
  have h_plus_reverse :=
    JacobianChallenge.single_smoothPath_plus_reverse_mem_stokesBoundaries
      (I := I) (X := X) β
  have h_sum :
      - triple_concat_smoothCycle γ α β h_αγ h_γβ_rev
        - JacobianChallenge.single_smoothPath_plus_reverse_smoothCycle β
        ∈ stokesBoundaries I X :=
    AddSubgroup.sub_mem _ h_neg_triple h_plus_reverse
  -- Show the cycle-level equality.
  have h_eq :
      - triple_concat_smoothCycle γ α β h_αγ h_γβ_rev
        - JacobianChallenge.single_smoothPath_plus_reverse_smoothCycle β
      = rebasing_smoothCycle γ α β h_αγ h_γβ_rev hα_src := by
    apply Subtype.ext
    rw [SmoothCycle.coe_sub, SmoothCycle.coe_neg]
    rw [triple_concat_smoothCycle_coe γ α β h_αγ h_γβ_rev,
        single_smoothPath_plus_reverse_smoothCycle_coe
          (I := I) (X := X) β,
        rebasing_smoothCycle_coe γ α β h_αγ h_γβ_rev hα_src]
    exact rebasing_chain_collapse γ α β h_αγ h_γβ_rev
  rw [← h_eq]
  exact h_sum

end JacobianChallenge

end
