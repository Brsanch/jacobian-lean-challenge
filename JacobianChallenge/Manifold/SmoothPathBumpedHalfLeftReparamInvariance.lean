/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexReparamLeftT2
import JacobianChallenge.Manifold.SmoothPathConstFromFace0
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary

set_option linter.unusedSectionVars false

/-! # Reparam-invariance for `bumpedHalfLeft`

Combines the two simplices `T₁, T₂` from
`Smooth2SimplexReparamLeftT1.lean` and `Smooth2SimplexReparamLeftT2.lean`
into the 2-chain `c := T₁ + T₂`, whose boundary (after diagonal
cancellation `face1 T₁ = face2 T₂`) is

```
∂c = single (const γ.tgt) + single γ + single γ.bumpedHalfLeft.reverse
       - single (const γ.src).
```

So this chain lies in `stokesBoundaries`. Combined with:

* `single (const γ.src) ∈ stokesBoundaries`,
* `single (const γ.tgt) ∈ stokesBoundaries`,
* `single γ.bumpedHalfLeft + single γ.bumpedHalfLeft.reverse
    ∈ stokesBoundaries` (path-plus-reverse identity),

we conclude

```
single γ - single γ.bumpedHalfLeft ∈ stokesBoundaries
```

i.e., the bumpedHalfLeft reparameterisation of `γ` is homologous
(mod Stokes-boundaries) to `γ`.

## What this file ships

* `boundary_T1_plus_T2_eq_full_chain` — the boundary chain identity.
* `T1_plus_T2_chain_mem_stokesBoundaries` — the full chain lies in
  `stokesBoundaries`.
* `bumpedHalfLeft_reparam_invariance` — the headline:
  `single γ - single γ.bumpedHalfLeft ∈ stokesBoundaries` (as a
  membership statement at the SmoothCycle level).

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (γ : SmoothPath I X)

/-! ## Boundary chain identity for T₁ + T₂ -/

/-- **The boundary of the 2-chain `Smooth2Chain.single T₁ + Smooth2Chain.single T₂`
in the SmoothChain.**

After diagonal cancellation (`face1 T₁ = face2 T₂`), the boundary
reduces to a sum of four singles:

```
single (const γ.tgt) + single γ + single γ.bumpedHalfLeft.reverse
  - single (const γ.src).
```
-/
theorem boundary_T1_plus_T2_eq_full_chain :
    Smooth2Chain.boundary₂
        (Smooth2Chain.single (Smooth2Simplex.ofReparamLeftT1 γ)
          + Smooth2Chain.single (Smooth2Simplex.ofReparamLeftT2 γ))
      = SmoothChain.single (SmoothPath.const I X γ.tgt)
        + SmoothChain.single γ
        + SmoothChain.single γ.bumpedHalfLeft.reverse
        - SmoothChain.single (SmoothPath.const I X γ.src) := by
  rw [map_add]
  rw [Smooth2Chain.boundary₂_single, Smooth2Chain.boundary₂_single]
  -- Boundary of each simplex:
  unfold Smooth2Simplex.boundary
  rw [face0_ofReparamLeftT1_eq_const_tgt, face2_ofReparamLeftT1_eq,
      face0_ofReparamLeftT2_eq_bumpedHalfLeftReverse,
      face1_ofReparamLeftT2_eq_const_src,
      face2_ofReparamLeftT2_eq_face1_ofReparamLeftT1]
  -- Now: (single (const γ.tgt) - single (face1 T₁) + single γ) +
  --      (single bumpedHalfLeft.reverse - single (const γ.src) + single (face1 T₁))
  -- The single (face1 T₁) cancels.
  abel

/-! ## The full chain lies in `stokesBoundaries` -/

/-- **The full chain is a smooth 1-cycle.** -/
lemma T1_plus_T2_chain_mem_smoothCycle :
    SmoothChain.single (SmoothPath.const I X γ.tgt)
      + SmoothChain.single γ
      + SmoothChain.single γ.bumpedHalfLeft.reverse
      - SmoothChain.single (SmoothPath.const I X γ.src)
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [← boundary_T1_plus_T2_eq_full_chain]
  rw [SmoothCycle.mem_iff]
  exact Smooth2Chain.boundary_boundary₂ _

/-- **Packaged SmoothCycle of the full chain.** -/
noncomputable def T1_plus_T2_chain_smoothCycle : SmoothCycle I X :=
  ⟨SmoothChain.single (SmoothPath.const I X γ.tgt)
    + SmoothChain.single γ
    + SmoothChain.single γ.bumpedHalfLeft.reverse
    - SmoothChain.single (SmoothPath.const I X γ.src),
    T1_plus_T2_chain_mem_smoothCycle γ⟩

/-- **The full chain lies in `stokesBoundaries`.** Witness:
`Smooth2Chain.single T₁ + Smooth2Chain.single T₂`. -/
theorem T1_plus_T2_chain_smoothCycle_mem_stokesBoundaries :
    T1_plus_T2_chain_smoothCycle γ ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofReparamLeftT1 γ)
            + Smooth2Chain.single (Smooth2Simplex.ofReparamLeftT2 γ), ?_⟩
  apply Subtype.ext
  show ((Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofReparamLeftT1 γ)
            + Smooth2Chain.single (Smooth2Simplex.ofReparamLeftT2 γ)) :
          SmoothCycle I X) : SmoothChain I X)
      = _
  rw [Smooth2Chain.boundary₂Cycle_coe]
  exact boundary_T1_plus_T2_eq_full_chain γ

/-! ## Reparam-invariance headline -/

/-- **`single γ - single γ.bumpedHalfLeft` is a smooth 1-cycle.** -/
lemma γ_minus_bumpedHalfLeft_mem_smoothCycle :
    SmoothChain.single γ - SmoothChain.single γ.bumpedHalfLeft
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single γ - SmoothChain.single γ.bumpedHalfLeft
        = SmoothChain.single γ + (-SmoothChain.single γ.bumpedHalfLeft)
        from sub_eq_add_neg _ _]
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_add, SmoothChain.boundary_neg,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle]
  simp [SmoothPath.bumpedHalfLeft_src, SmoothPath.bumpedHalfLeft_tgt]

/-- **Packaged SmoothCycle.** -/
noncomputable def γ_minus_bumpedHalfLeft_smoothCycle :
    SmoothCycle I X :=
  ⟨SmoothChain.single γ - SmoothChain.single γ.bumpedHalfLeft,
    γ_minus_bumpedHalfLeft_mem_smoothCycle γ⟩

@[simp] lemma γ_minus_bumpedHalfLeft_smoothCycle_coe :
    (γ_minus_bumpedHalfLeft_smoothCycle γ : SmoothChain I X)
      = SmoothChain.single γ - SmoothChain.single γ.bumpedHalfLeft := rfl

/-- Chain-level identity that the sum of cycles collapses to
`single γ - single γ.bumpedHalfLeft`. Helper for `bumpedHalfLeft_reparam_invariance`. -/
private lemma reparam_chain_collapse :
    (SmoothChain.single (SmoothPath.const I X γ.tgt)
        + SmoothChain.single γ
        + SmoothChain.single γ.bumpedHalfLeft.reverse
        - SmoothChain.single (SmoothPath.const I X γ.src))
      + SmoothChain.single (SmoothPath.const I X γ.src)
      - SmoothChain.single (SmoothPath.const I X γ.tgt)
      - (SmoothChain.single γ.bumpedHalfLeft
          + SmoothChain.single γ.bumpedHalfLeft.reverse)
      = SmoothChain.single γ - SmoothChain.single γ.bumpedHalfLeft := by
  abel

/-- **Reparam-invariance for bumpedHalfLeft.**

For any smooth path `γ`, the chain `single γ - single γ.bumpedHalfLeft`
lies in `stokesBoundaries`. Equivalently, `γ` and `γ.bumpedHalfLeft`
represent the same homology class in the canonical Stokes H₁ quotient. -/
theorem bumpedHalfLeft_reparam_invariance :
    γ_minus_bumpedHalfLeft_smoothCycle γ ∈ stokesBoundaries I X := by
  -- Strategy: express `single γ - single γ.bumpedHalfLeft` as a ℤ-linear
  -- combination of cycles in stokesBoundaries.
  have h1 := T1_plus_T2_chain_smoothCycle_mem_stokesBoundaries (I := I) (X := X) γ
  have h2 :=
    JacobianChallenge.single_smoothPath_const_smoothCycle_mem_stokesBoundaries
      (I := I) (X := X) γ.src
  have h3 :=
    JacobianChallenge.single_smoothPath_const_smoothCycle_mem_stokesBoundaries
      (I := I) (X := X) γ.tgt
  have h4 :=
    JacobianChallenge.single_smoothPath_plus_reverse_mem_stokesBoundaries
      (I := I) (X := X) γ.bumpedHalfLeft
  have h_sum : T1_plus_T2_chain_smoothCycle γ
      + JacobianChallenge.single_smoothPath_const_smoothCycle γ.src
      - JacobianChallenge.single_smoothPath_const_smoothCycle γ.tgt
      - JacobianChallenge.single_smoothPath_plus_reverse_smoothCycle
          γ.bumpedHalfLeft
      ∈ stokesBoundaries I X :=
    AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _
        (AddSubgroup.add_mem _ h1 h2) h3) h4
  -- Show the cycle-level equality directly via Subtype.ext.
  have h_eq :
      T1_plus_T2_chain_smoothCycle γ
        + JacobianChallenge.single_smoothPath_const_smoothCycle γ.src
        - JacobianChallenge.single_smoothPath_const_smoothCycle γ.tgt
        - JacobianChallenge.single_smoothPath_plus_reverse_smoothCycle
            γ.bumpedHalfLeft
      = γ_minus_bumpedHalfLeft_smoothCycle γ := by
    apply Subtype.ext
    rw [SmoothCycle.coe_sub, SmoothCycle.coe_sub, SmoothCycle.coe_add]
    -- Each .toSmoothChain coercion reduces by `rfl` to the underlying chain.
    -- Use rewrites via the chain-extraction lemmas.
    rw [show (T1_plus_T2_chain_smoothCycle γ : SmoothChain I X)
            = SmoothChain.single (SmoothPath.const I X γ.tgt)
              + SmoothChain.single γ
              + SmoothChain.single γ.bumpedHalfLeft.reverse
              - SmoothChain.single (SmoothPath.const I X γ.src)
          from rfl,
        single_smoothPath_const_smoothCycle_coe (I := I) (X := X) γ.src,
        single_smoothPath_const_smoothCycle_coe (I := I) (X := X) γ.tgt,
        single_smoothPath_plus_reverse_smoothCycle_coe
          (I := I) (X := X) γ.bumpedHalfLeft,
        γ_minus_bumpedHalfLeft_smoothCycle_coe γ]
    exact reparam_chain_collapse γ
  rw [← h_eq]
  exact h_sum

end JacobianChallenge

end
