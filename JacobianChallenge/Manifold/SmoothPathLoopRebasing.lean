/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathRebasingFull

set_option linter.unusedSectionVars false

/-! # Loop-rebasing identity in stokesBoundaries

**Specialization of `rebasing_in_stokesBoundaries` to a smooth loop.**

For a smooth loop `γ : SmoothPath I X` (i.e., `γ.src = γ.tgt = a`) and
any smooth based path `α : p₀ → a`,

```
single γ - single (α ⋆ γ ⋆ α.reverse) ∈ stokesBoundaries I X.
```

(With `α.tgt = a = γ.src` automatic from the based-path hypothesis,
and the rebasing corrections `single α - single α = 0` collapsing.)

Equivalently: `[γ] = [α ⋆ γ ⋆ α.reverse]` in the canonical Stokes H₁
quotient. **Every smooth loop at `a` is homologous to a based smooth
loop at `p₀`.**

This is the structural identity that reduces "every smooth loop on a
simply-connected manifold bounds" to "every BASED smooth loop at a
fixed basepoint bounds".

## What this file ships

* `loop_rebasing_chain_mem_smoothCycle` — chain is a 1-cycle.
* `loop_rebasing_smoothCycle` — packaged.
* `loop_rebasing_in_stokesBoundaries` — the headline.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (γ : SmoothPath I X) (α : SmoothPath I X)

/-- For a smooth loop γ (γ.src = γ.tgt) and based path α (α.tgt = γ.src),
the chain `single γ - single (α ⋆ γ ⋆ α.reverse)` is a smooth 1-cycle. -/
lemma loop_rebasing_chain_mem_smoothCycle
    (h_loop : γ.src = γ.tgt) (h_αγ : α.tgt = γ.src) :
    SmoothChain.single γ
      - SmoothChain.single
          (α.concat (γ.concat α.reverse
              (by rw [SmoothPath.reverse_src]; exact h_αγ ▸ h_loop.symm))
            (by rw [SmoothPath.concat_src]; exact h_αγ))
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single γ - SmoothChain.single
            (α.concat (γ.concat α.reverse
                (by rw [SmoothPath.reverse_src]; exact h_αγ ▸ h_loop.symm))
              (by rw [SmoothPath.concat_src]; exact h_αγ))
        = SmoothChain.single γ
          + (-SmoothChain.single
              (α.concat (γ.concat α.reverse
                  (by rw [SmoothPath.reverse_src]; exact h_αγ ▸ h_loop.symm))
                (by rw [SmoothPath.concat_src]; exact h_αγ))) from
      sub_eq_add_neg _ _]
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_add, SmoothChain.boundary_neg,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle]
  simp [SmoothPath.concat_src, SmoothPath.concat_tgt, SmoothPath.reverse_src,
    SmoothPath.reverse_tgt, h_αγ, h_loop]

/-- Packaged loop-rebasing SmoothCycle. -/
noncomputable def loop_rebasing_smoothCycle
    (h_loop : γ.src = γ.tgt) (h_αγ : α.tgt = γ.src) : SmoothCycle I X :=
  ⟨SmoothChain.single γ
    - SmoothChain.single
        (α.concat (γ.concat α.reverse
            (by rw [SmoothPath.reverse_src]; exact h_αγ ▸ h_loop.symm))
          (by rw [SmoothPath.concat_src]; exact h_αγ)),
    loop_rebasing_chain_mem_smoothCycle γ α h_loop h_αγ⟩

/-! ## Headline -/

/-- **Loop-rebasing identity.**

For any smooth loop `γ : SmoothPath I X` (with `γ.src = γ.tgt`) and any
smooth based path `α : p₀ → γ.src`,

```
single γ - single (α ⋆ γ ⋆ α.reverse) ∈ stokesBoundaries I X.
```

Equivalently, every smooth loop is homologous (mod stokes-boundaries)
to a based smooth loop at the chosen basepoint `p₀`. -/
theorem loop_rebasing_in_stokesBoundaries
    (h_loop : γ.src = γ.tgt) (h_αγ : α.tgt = γ.src) :
    loop_rebasing_smoothCycle γ α h_loop h_αγ ∈ stokesBoundaries I X := by
  -- Apply the full rebasing identity with β := α.
  -- Note: h_γβ_rev needs γ.tgt = α.reverse.src = α.tgt, which is h_αγ.symm
  -- after using h_loop.
  have h_γβ_rev : γ.tgt = α.reverse.src := by
    rw [SmoothPath.reverse_src]
    exact h_αγ ▸ h_loop.symm
  have hα_src : α.src = α.src := rfl
  have h_rebase :=
    rebasing_in_stokesBoundaries (I := I) (X := X)
      γ α α h_αγ h_γβ_rev hα_src
  -- Show loop_rebasing_smoothCycle γ α h_loop h_αγ
  --   = rebasing_smoothCycle γ α α h_αγ h_γβ_rev hα_src.
  -- Underlying chain difference:
  --   loop_rebasing: single γ - single (α ⋆ γ ⋆ α.reverse).
  --   rebasing γ α α: single γ - single (α ⋆ γ ⋆ α.reverse) + single α - single α.
  -- These differ by `single α - single α = 0`, so are equal.
  have h_eq :
      rebasing_smoothCycle γ α α h_αγ h_γβ_rev hα_src
        = loop_rebasing_smoothCycle γ α h_loop h_αγ := by
    apply Subtype.ext
    rw [rebasing_smoothCycle_coe γ α α h_αγ h_γβ_rev hα_src]
    show SmoothChain.single γ
          - SmoothChain.single (α.concat (γ.concat α.reverse h_γβ_rev) _)
          + SmoothChain.single α
          - SmoothChain.single α
        = (loop_rebasing_smoothCycle γ α h_loop h_αγ : SmoothChain I X)
    show _ = SmoothChain.single γ
              - SmoothChain.single
                (α.concat (γ.concat α.reverse _)
                  (by rw [SmoothPath.concat_src]; exact h_αγ))
    abel
  rw [← h_eq]
  exact h_rebase

end JacobianChallenge

end
