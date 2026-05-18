/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConcatFaceIdent
import JacobianChallenge.Manifold.SmoothPathBumpedHalfLeftReparamInvariance
import JacobianChallenge.Manifold.SmoothPathBumpedHalfRightReparamInvariance

set_option linter.unusedSectionVars false

/-! # Concat-additivity in stokesBoundaries

**Headline.** For any compatible smooth paths `γ, δ : SmoothPath I X`
with `γ.tgt = δ.src`,

```
single (γ.concat δ h) - single γ - single δ ∈ stokesBoundaries I X.
```

I.e., concatenation of smooth paths is **additive** in the canonical
Stokes H₁ quotient.

## Proof strategy

Combines three previously-established stokes-boundary memberships:

1. **Concat-face-ident** (from
   `Smooth2SimplexConcatFaceIdent.lean`'s
   `fully_identified_chain_concat_smoothCycle_mem_stokesBoundaries`):

   ```
   single δ.bumpedHalfRight - single (γ.concat δ h) + single γ.bumpedHalfLeft
     ∈ stokesBoundaries.
   ```

2. **Left reparam-invariance** (from
   `SmoothPathBumpedHalfLeftReparamInvariance.lean`'s
   `bumpedHalfLeft_reparam_invariance`):

   ```
   single γ - single γ.bumpedHalfLeft ∈ stokesBoundaries.
   ```

3. **Right reparam-invariance** (from
   `SmoothPathBumpedHalfRightReparamInvariance.lean`'s
   `bumpedHalfRight_reparam_invariance`):

   ```
   single δ - single δ.bumpedHalfRight ∈ stokesBoundaries.
   ```

Linear combination (1) negated + (2) + (3) gives:

```
- single δ.bumpedHalfRight + single (γ.concat δ h) - single γ.bumpedHalfLeft
  + single γ - single γ.bumpedHalfLeft + single δ - single δ.bumpedHalfRight
  ∈ stokesBoundaries.
```

Wait — let me re-check the signs. Negating (1):
- `-(single δ.bumpedHalfRight - single (γ.concat δ h) + single γ.bumpedHalfLeft)
   = single (γ.concat δ h) - single δ.bumpedHalfRight - single γ.bumpedHalfLeft`.

Adding (2): `(- (1)) + (2)`:
`single (γ.concat δ h) - single δ.bumpedHalfRight - single γ.bumpedHalfLeft
 + single γ - single γ.bumpedHalfLeft`.

That's still has `-2 single γ.bumpedHalfLeft`. Let me redo:

Actually we want: `single (γ.concat δ h) - single γ - single δ`. Express:

```
single (γ.concat δ h) - single γ - single δ
  = - (1) - (2) - (3)
  = -(single δ.bumpedHalfRight - single (γ.concat δ h) + single γ.bumpedHalfLeft)
    - (single γ - single γ.bumpedHalfLeft)
    - (single δ - single δ.bumpedHalfRight)
  = single (γ.concat δ h) - single δ.bumpedHalfRight - single γ.bumpedHalfLeft
    - single γ + single γ.bumpedHalfLeft
    - single δ + single δ.bumpedHalfRight
  = single (γ.concat δ h) - single γ - single δ.    ✓
```

So the combination is `- (1) - (2) - (3)`.

## What this file ships

* `concat_additive_chain_mem_smoothCycle`.
* `concat_additive_smoothCycle`.
* `concat_additive_in_stokesBoundaries` — the headline.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (γ δ : SmoothPath I X) (h : γ.tgt = δ.src)

/-! ## The concat-additive cycle -/

/-- **The chain `single (γ.concat δ h) - single γ - single δ` is a
smooth 1-cycle.** Boundary computation: each `single γ_i` boundary
contributes `δ_{tgt} - δ_{src}` with appropriate signs that cancel. -/
lemma concat_additive_chain_mem_smoothCycle :
    SmoothChain.single (γ.concat δ h)
      - SmoothChain.single γ
      - SmoothChain.single δ
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single (γ.concat δ h)
        - SmoothChain.single γ - SmoothChain.single δ
        = SmoothChain.single (γ.concat δ h)
          + (-SmoothChain.single γ) + (-SmoothChain.single δ) from by abel]
  rw [SmoothCycle.mem_iff,
      SmoothChain.boundary_add,
      SmoothChain.boundary_add,
      SmoothChain.boundary_neg,
      SmoothChain.boundary_neg,
      SmoothChain.boundary_single,
      SmoothChain.boundary_single,
      SmoothChain.boundary_single,
      SmoothChain.boundarySingle,
      SmoothChain.boundarySingle,
      SmoothChain.boundarySingle]
  simp [SmoothPath.concat_src, SmoothPath.concat_tgt, h]

/-- **Packaged SmoothCycle for the concat-additive chain.** -/
noncomputable def concat_additive_smoothCycle :
    SmoothCycle I X :=
  ⟨SmoothChain.single (γ.concat δ h)
    - SmoothChain.single γ
    - SmoothChain.single δ,
    concat_additive_chain_mem_smoothCycle γ δ h⟩

@[simp] lemma concat_additive_smoothCycle_coe :
    (concat_additive_smoothCycle γ δ h : SmoothChain I X)
      = SmoothChain.single (γ.concat δ h)
        - SmoothChain.single γ
        - SmoothChain.single δ := rfl

/-! ## Chain-level cancellation lemma -/

/-- Algebraic chain-level identity needed for the concat-additivity
combination. -/
private lemma concat_additivity_chain_collapse :
    - (SmoothChain.single δ.bumpedHalfRight
        - SmoothChain.single (γ.concat δ h)
        + SmoothChain.single γ.bumpedHalfLeft)
      - (SmoothChain.single γ - SmoothChain.single γ.bumpedHalfLeft)
      - (SmoothChain.single δ - SmoothChain.single δ.bumpedHalfRight)
      = SmoothChain.single (γ.concat δ h)
        - SmoothChain.single γ
        - SmoothChain.single δ := by
  abel

/-! ## Headline: concat additivity in stokesBoundaries -/

/-- **Concat-additivity in `stokesBoundaries`.**

For any compatible smooth paths `γ, δ : SmoothPath I X` with
`γ.tgt = δ.src`, the chain `single (γ.concat δ h) - single γ - single δ`
(packaged as a SmoothCycle) lies in `stokesBoundaries I X`.

Equivalently, in the canonical Stokes H₁ quotient,
`[γ.concat δ h] = [γ] + [δ]`. -/
theorem concat_additive_in_stokesBoundaries :
    concat_additive_smoothCycle γ δ h ∈ stokesBoundaries I X := by
  -- Pull in the three stokes-boundary memberships.
  have h_face_ident :=
    fully_identified_chain_concat_smoothCycle_mem_stokesBoundaries
      (I := I) (X := X) γ δ h
  have h_left := bumpedHalfLeft_reparam_invariance (I := I) (X := X) γ
  have h_right := bumpedHalfRight_reparam_invariance (I := I) (X := X) δ
  -- Linear combination: - (face_ident) - (left) - (right).
  have h_neg_face := AddSubgroup.neg_mem _ h_face_ident
  have h_sum :
      - fully_identified_chain_concat_smoothCycle γ δ h
        - γ_minus_bumpedHalfLeft_smoothCycle γ
        - δ_minus_bumpedHalfRight_smoothCycle δ
        ∈ stokesBoundaries I X :=
    AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ h_neg_face h_left) h_right
  -- Show this equals concat_additive_smoothCycle γ δ h at the cycle level.
  have h_eq :
      - fully_identified_chain_concat_smoothCycle γ δ h
        - γ_minus_bumpedHalfLeft_smoothCycle γ
        - δ_minus_bumpedHalfRight_smoothCycle δ
      = concat_additive_smoothCycle γ δ h := by
    apply Subtype.ext
    rw [SmoothCycle.coe_sub, SmoothCycle.coe_sub, SmoothCycle.coe_neg]
    -- Unfold the three cycle-coe.
    rw [show (fully_identified_chain_concat_smoothCycle γ δ h
              : SmoothChain I X)
          = SmoothChain.single δ.bumpedHalfRight
            - SmoothChain.single (γ.concat δ h)
            + SmoothChain.single γ.bumpedHalfLeft from rfl,
        γ_minus_bumpedHalfLeft_smoothCycle_coe γ,
        δ_minus_bumpedHalfRight_smoothCycle_coe δ,
        concat_additive_smoothCycle_coe γ δ h]
    exact concat_additivity_chain_collapse γ δ h
  rw [← h_eq]
  exact h_sum

end JacobianChallenge

end
