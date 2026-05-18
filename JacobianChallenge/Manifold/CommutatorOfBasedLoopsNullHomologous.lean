/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SmoothPathConcatAdditivityStokes
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # The commutator of two based loops is null-homologous

For any two smooth based loops `α, β : SmoothPath I X` at a common
basepoint `p₀ : X`, the **commutator path**

```
[α, β] := α ⋆ β ⋆ α⁻¹ ⋆ β⁻¹
```

is also a smooth based loop at `p₀`, and its `single` lies in
`stokesBoundaries I X`.

This is a real homological identity validating the smooth-Hurewicz
framework: it is the classical statement that **`H₁` is abelian**
applied to a specific commutator. The proof composes three existing
chips:

1. `concat_additive_in_stokesBoundaries` — for compatible smooth
   paths γ, δ: `single (γ.concat δ) - single γ - single δ ∈
   stokesBoundaries`.

2. `single_smoothPath_plus_reverse_mem_stokesBoundaries` — for any
   smooth path γ: `single γ + single γ.reverse ∈ stokesBoundaries`.

3. Three applications of (1) to expand the 4-fold concat, then two
   applications of (2) to cancel `single α + single α.reverse` and
   `single β + single β.reverse`, leaving the zero chain mod
   stokes-boundaries.

## What this file ships

* `inverseConcatLoop α` — the loop `α ⋆ α⁻¹`.
* `single_inverseConcatLoop_mem_stokesBoundaries` — `single (α ⋆ α⁻¹)
  ∈ stokesBoundaries` (the inverse-pair specialization).
* `commutatorLoop α β h_α_loop h_β_loop` — the commutator loop
  `α ⋆ β ⋆ α⁻¹ ⋆ β⁻¹`.
* `single_commutatorLoop_mem_stokesBoundaries` — `single (commutator
  α β) ∈ stokesBoundaries`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-! ## Inverse-pair specialization -/

/-- **The inverse-concat loop `α ⋆ α⁻¹`** for a smooth path α : a → b. -/
noncomputable def inverseConcatLoop (α : SmoothPath I X) : SmoothPath I X :=
  α.concat α.reverse (by rw [SmoothPath.reverse_src])

@[simp] lemma inverseConcatLoop_src (α : SmoothPath I X) :
    (inverseConcatLoop α).src = α.src := by
  change (α.concat α.reverse _).src = α.src
  rw [SmoothPath.concat_src]

@[simp] lemma inverseConcatLoop_tgt (α : SmoothPath I X) :
    (inverseConcatLoop α).tgt = α.src := by
  change (α.concat α.reverse _).tgt = α.src
  rw [SmoothPath.concat_tgt, SmoothPath.reverse_tgt]

/-- The inverse-concat loop is a based loop at `α.src`. -/
lemma inverseConcatLoop_is_loop (α : SmoothPath I X) :
    (inverseConcatLoop α).src = (inverseConcatLoop α).tgt := by
  rw [inverseConcatLoop_src, inverseConcatLoop_tgt]

/-- **The inverse-pair loop `α ⋆ α⁻¹` is null-homologous.** Its
`single` (packaged as a SmoothCycle) lies in `stokesBoundaries`.

Proof: concat additivity gives `single (α ⋆ α⁻¹) - single α - single
α⁻¹ ∈ stokes`; reverse cancellation gives `single α + single α⁻¹ ∈
stokes`. Adding the two memberships gives `single (α ⋆ α⁻¹) ∈ stokes`. -/
theorem single_inverseConcatLoop_mem_stokesBoundaries (α : SmoothPath I X) :
    single_smoothLoop_smoothCycle (inverseConcatLoop α)
        (inverseConcatLoop_is_loop α) ∈ stokesBoundaries I X := by
  -- Pull in the two memberships.
  have h_concat :=
    concat_additive_in_stokesBoundaries (I := I) (X := X) α α.reverse
      (by rw [SmoothPath.reverse_src])
  have h_reverse :=
    single_smoothPath_plus_reverse_mem_stokesBoundaries (I := I) (X := X) α
  -- Sum: gives `single (α ⋆ α⁻¹) ∈ stokes`.
  have h_sum :
      (concat_additive_smoothCycle (I := I) (X := X) α α.reverse
          (by rw [SmoothPath.reverse_src]))
        + (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) α)
        ∈ stokesBoundaries I X :=
    AddSubgroup.add_mem _ h_concat h_reverse
  -- Show the sum equals `single (inverseConcatLoop α)` at the cycle level.
  have h_eq :
      (concat_additive_smoothCycle (I := I) (X := X) α α.reverse
          (by rw [SmoothPath.reverse_src]))
        + (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) α)
      = single_smoothLoop_smoothCycle (inverseConcatLoop α)
          (inverseConcatLoop_is_loop α) := by
    apply Subtype.ext
    rw [SmoothCycle.coe_add,
        concat_additive_smoothCycle_coe,
        single_smoothPath_plus_reverse_smoothCycle_coe,
        single_smoothLoop_smoothCycle_coe]
    change SmoothChain.single (α.concat α.reverse _)
          - SmoothChain.single α - SmoothChain.single α.reverse
          + (SmoothChain.single α + SmoothChain.single α.reverse)
        = SmoothChain.single (α.concat α.reverse _)
    abel
  rw [← h_eq]
  exact h_sum

/-! ## Commutator of two based loops -/

section Commutator

variable (p₀ : X) (α β : SmoothPath I X)
  (h_α_src : α.src = p₀) (h_α_tgt : α.tgt = p₀)
  (h_β_src : β.src = p₀) (h_β_tgt : β.tgt = p₀)

include h_α_src h_α_tgt h_β_src h_β_tgt

/-- **The commutator loop `α ⋆ β ⋆ α⁻¹ ⋆ β⁻¹`** at the common
basepoint `p₀`. Three nested concatenations. -/
noncomputable def commutatorLoop : SmoothPath I X :=
  ((α.concat β (by rw [h_α_tgt, h_β_src])).concat α.reverse
      (by rw [SmoothPath.concat_tgt, h_β_tgt, SmoothPath.reverse_src,
              h_α_tgt])).concat β.reverse
      (by rw [SmoothPath.concat_tgt, SmoothPath.reverse_tgt, h_α_src,
              SmoothPath.reverse_src, h_β_tgt])

lemma commutatorLoop_src :
    (commutatorLoop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt).src = p₀ := by
  change (((α.concat β _).concat α.reverse _).concat β.reverse _).src = p₀
  rw [SmoothPath.concat_src, SmoothPath.concat_src, SmoothPath.concat_src,
      h_α_src]

lemma commutatorLoop_tgt :
    (commutatorLoop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt).tgt = p₀ := by
  change (((α.concat β _).concat α.reverse _).concat β.reverse _).tgt = p₀
  rw [SmoothPath.concat_tgt, SmoothPath.reverse_tgt, h_β_src]

lemma commutatorLoop_is_loop :
    (commutatorLoop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt).src
      = (commutatorLoop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt).tgt := by
  rw [commutatorLoop_src, commutatorLoop_tgt]

/-- **The commutator of two based loops at `p₀` is null-homologous.**

The chain `single ([α, β])` (packaged as a SmoothCycle, with `[α, β] =
α ⋆ β ⋆ α⁻¹ ⋆ β⁻¹`) lies in `stokesBoundaries I X`.

Proof: three applications of `concat_additive_in_stokesBoundaries`
unfold the 4-fold concat as `single α + single β + single α.reverse +
single β.reverse` mod stokes; two applications of
`single_smoothPath_plus_reverse_mem_stokesBoundaries` cancel the
α/α⁻¹ and β/β⁻¹ pairs, leaving 0 mod stokes. -/
theorem single_commutatorLoop_mem_stokesBoundaries :
    single_smoothLoop_smoothCycle
        (commutatorLoop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt)
        (commutatorLoop_is_loop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt)
      ∈ stokesBoundaries I X := by
  -- Three concat-additivity memberships.
  -- (i) outer concat: γ₂ := γ_1 ⋆ α.reverse, where γ_1 := α ⋆ β.
  set h_αβ : α.tgt = β.src := by rw [h_α_tgt, h_β_src]
  set h_γ1_αrev : (α.concat β h_αβ).tgt = α.reverse.src := by
    rw [SmoothPath.concat_tgt, h_β_tgt, SmoothPath.reverse_src, h_α_tgt]
  set h_γ2_βrev :
      ((α.concat β h_αβ).concat α.reverse h_γ1_αrev).tgt = β.reverse.src := by
    rw [SmoothPath.concat_tgt, SmoothPath.reverse_tgt, h_α_src,
        SmoothPath.reverse_src, h_β_tgt]
  have h_inner :=
    concat_additive_in_stokesBoundaries (I := I) (X := X) α β h_αβ
  have h_middle :=
    concat_additive_in_stokesBoundaries (I := I) (X := X)
      (α.concat β h_αβ) α.reverse h_γ1_αrev
  have h_outer :=
    concat_additive_in_stokesBoundaries (I := I) (X := X)
      ((α.concat β h_αβ).concat α.reverse h_γ1_αrev) β.reverse h_γ2_βrev
  -- Two reverse-cancellation memberships.
  have h_α_rev :=
    single_smoothPath_plus_reverse_mem_stokesBoundaries (I := I) (X := X) α
  have h_β_rev :=
    single_smoothPath_plus_reverse_mem_stokesBoundaries (I := I) (X := X) β
  -- Sum all five.
  have h_sum :
      (concat_additive_smoothCycle (I := I) (X := X) α β h_αβ)
        + (concat_additive_smoothCycle (I := I) (X := X)
            (α.concat β h_αβ) α.reverse h_γ1_αrev)
        + (concat_additive_smoothCycle (I := I) (X := X)
            ((α.concat β h_αβ).concat α.reverse h_γ1_αrev) β.reverse h_γ2_βrev)
        + (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) α)
        + (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) β)
      ∈ stokesBoundaries I X := by
    apply AddSubgroup.add_mem _ _ h_β_rev
    apply AddSubgroup.add_mem _ _ h_α_rev
    apply AddSubgroup.add_mem _ _ h_outer
    apply AddSubgroup.add_mem _ h_inner h_middle
  -- The sum equals single (commutatorLoop) at the cycle level.
  have h_eq :
      (concat_additive_smoothCycle (I := I) (X := X) α β h_αβ)
        + (concat_additive_smoothCycle (I := I) (X := X)
            (α.concat β h_αβ) α.reverse h_γ1_αrev)
        + (concat_additive_smoothCycle (I := I) (X := X)
            ((α.concat β h_αβ).concat α.reverse h_γ1_αrev) β.reverse h_γ2_βrev)
        + (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) α)
        + (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) β)
      = single_smoothLoop_smoothCycle
          (commutatorLoop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt)
          (commutatorLoop_is_loop p₀ α β h_α_src h_α_tgt h_β_src h_β_tgt) := by
    apply Subtype.ext
    rw [SmoothCycle.coe_add, SmoothCycle.coe_add, SmoothCycle.coe_add,
        SmoothCycle.coe_add,
        concat_additive_smoothCycle_coe,
        concat_additive_smoothCycle_coe,
        concat_additive_smoothCycle_coe,
        single_smoothPath_plus_reverse_smoothCycle_coe,
        single_smoothPath_plus_reverse_smoothCycle_coe,
        single_smoothLoop_smoothCycle_coe]
    -- Unfold `commutatorLoop` on the RHS so abel can close.
    change SmoothChain.single (α.concat β h_αβ)
          - SmoothChain.single α - SmoothChain.single β
        + (SmoothChain.single ((α.concat β h_αβ).concat α.reverse h_γ1_αrev)
            - SmoothChain.single (α.concat β h_αβ) - SmoothChain.single α.reverse)
        + (SmoothChain.single (((α.concat β h_αβ).concat α.reverse h_γ1_αrev).concat
              β.reverse h_γ2_βrev)
            - SmoothChain.single ((α.concat β h_αβ).concat α.reverse h_γ1_αrev)
            - SmoothChain.single β.reverse)
        + (SmoothChain.single α + SmoothChain.single α.reverse)
        + (SmoothChain.single β + SmoothChain.single β.reverse)
      = SmoothChain.single (((α.concat β h_αβ).concat α.reverse h_γ1_αrev).concat
            β.reverse h_γ2_βrev)
    abel
  rw [← h_eq]
  exact h_sum

end Commutator

end JacobianChallenge

end
