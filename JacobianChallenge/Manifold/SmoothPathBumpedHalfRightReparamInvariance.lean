/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexReparamRightT2
import JacobianChallenge.Manifold.SmoothPathConstFromFace0
import JacobianChallenge.Manifold.SmoothPathReverseStokesBoundary

set_option linter.unusedSectionVars false

/-! # Reparam-invariance for `bumpedHalfRight`

Symmetric to `SmoothPathBumpedHalfLeftReparamInvariance.lean`:

```
single δ - single δ.bumpedHalfRight ∈ stokesBoundaries I X.
```

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (δ : SmoothPath I X)

/-! ## Boundary chain identity for T₁' + T₂' (right variant) -/

theorem boundary_T1_plus_T2_right_eq_full_chain :
    Smooth2Chain.boundary₂
        (Smooth2Chain.single (Smooth2Simplex.ofReparamRightT1 δ)
          + Smooth2Chain.single (Smooth2Simplex.ofReparamRightT2 δ))
      = SmoothChain.single (SmoothPath.const I X δ.tgt)
        + SmoothChain.single δ
        + SmoothChain.single δ.bumpedHalfRight.reverse
        - SmoothChain.single (SmoothPath.const I X δ.src) := by
  rw [map_add]
  rw [Smooth2Chain.boundary₂_single, Smooth2Chain.boundary₂_single]
  unfold Smooth2Simplex.boundary
  rw [face0_ofReparamRightT1_eq_const_tgt, face2_ofReparamRightT1_eq,
      face0_ofReparamRightT2_eq_bumpedHalfRightReverse,
      face1_ofReparamRightT2_eq_const_src,
      face2_ofReparamRightT2_eq_face1_ofReparamRightT1]
  abel

lemma T1_plus_T2_right_chain_mem_smoothCycle :
    SmoothChain.single (SmoothPath.const I X δ.tgt)
      + SmoothChain.single δ
      + SmoothChain.single δ.bumpedHalfRight.reverse
      - SmoothChain.single (SmoothPath.const I X δ.src)
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [← boundary_T1_plus_T2_right_eq_full_chain]
  rw [SmoothCycle.mem_iff]
  exact Smooth2Chain.boundary_boundary₂ _

noncomputable def T1_plus_T2_right_chain_smoothCycle : SmoothCycle I X :=
  ⟨SmoothChain.single (SmoothPath.const I X δ.tgt)
    + SmoothChain.single δ
    + SmoothChain.single δ.bumpedHalfRight.reverse
    - SmoothChain.single (SmoothPath.const I X δ.src),
    T1_plus_T2_right_chain_mem_smoothCycle δ⟩

theorem T1_plus_T2_right_chain_smoothCycle_mem_stokesBoundaries :
    T1_plus_T2_right_chain_smoothCycle δ ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofReparamRightT1 δ)
            + Smooth2Chain.single (Smooth2Simplex.ofReparamRightT2 δ), ?_⟩
  apply Subtype.ext
  show ((Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofReparamRightT1 δ)
            + Smooth2Chain.single (Smooth2Simplex.ofReparamRightT2 δ)) :
          SmoothCycle I X) : SmoothChain I X)
      = _
  rw [Smooth2Chain.boundary₂Cycle_coe]
  exact boundary_T1_plus_T2_right_eq_full_chain δ

/-! ## Reparam-invariance headline (right variant) -/

lemma δ_minus_bumpedHalfRight_mem_smoothCycle :
    SmoothChain.single δ - SmoothChain.single δ.bumpedHalfRight
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [show SmoothChain.single δ - SmoothChain.single δ.bumpedHalfRight
        = SmoothChain.single δ + (-SmoothChain.single δ.bumpedHalfRight)
        from sub_eq_add_neg _ _]
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_add, SmoothChain.boundary_neg,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle]
  simp [SmoothPath.bumpedHalfRight_src, SmoothPath.bumpedHalfRight_tgt]

noncomputable def δ_minus_bumpedHalfRight_smoothCycle :
    SmoothCycle I X :=
  ⟨SmoothChain.single δ - SmoothChain.single δ.bumpedHalfRight,
    δ_minus_bumpedHalfRight_mem_smoothCycle δ⟩

@[simp] lemma δ_minus_bumpedHalfRight_smoothCycle_coe :
    (δ_minus_bumpedHalfRight_smoothCycle δ : SmoothChain I X)
      = SmoothChain.single δ - SmoothChain.single δ.bumpedHalfRight := rfl

private lemma reparam_right_chain_collapse :
    (SmoothChain.single (SmoothPath.const I X δ.tgt)
        + SmoothChain.single δ
        + SmoothChain.single δ.bumpedHalfRight.reverse
        - SmoothChain.single (SmoothPath.const I X δ.src))
      + SmoothChain.single (SmoothPath.const I X δ.src)
      - SmoothChain.single (SmoothPath.const I X δ.tgt)
      - (SmoothChain.single δ.bumpedHalfRight
          + SmoothChain.single δ.bumpedHalfRight.reverse)
      = SmoothChain.single δ - SmoothChain.single δ.bumpedHalfRight := by
  abel

/-- **Reparam-invariance for bumpedHalfRight.**

For any smooth path `δ`, `single δ - single δ.bumpedHalfRight ∈ stokesBoundaries`. -/
theorem bumpedHalfRight_reparam_invariance :
    δ_minus_bumpedHalfRight_smoothCycle δ ∈ stokesBoundaries I X := by
  have h1 :=
    T1_plus_T2_right_chain_smoothCycle_mem_stokesBoundaries (I := I) (X := X) δ
  have h2 :=
    JacobianChallenge.single_smoothPath_const_smoothCycle_mem_stokesBoundaries
      (I := I) (X := X) δ.src
  have h3 :=
    JacobianChallenge.single_smoothPath_const_smoothCycle_mem_stokesBoundaries
      (I := I) (X := X) δ.tgt
  have h4 :=
    JacobianChallenge.single_smoothPath_plus_reverse_mem_stokesBoundaries
      (I := I) (X := X) δ.bumpedHalfRight
  have h_sum : T1_plus_T2_right_chain_smoothCycle δ
      + JacobianChallenge.single_smoothPath_const_smoothCycle δ.src
      - JacobianChallenge.single_smoothPath_const_smoothCycle δ.tgt
      - JacobianChallenge.single_smoothPath_plus_reverse_smoothCycle
          δ.bumpedHalfRight
      ∈ stokesBoundaries I X :=
    AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _
        (AddSubgroup.add_mem _ h1 h2) h3) h4
  have h_eq :
      T1_plus_T2_right_chain_smoothCycle δ
        + JacobianChallenge.single_smoothPath_const_smoothCycle δ.src
        - JacobianChallenge.single_smoothPath_const_smoothCycle δ.tgt
        - JacobianChallenge.single_smoothPath_plus_reverse_smoothCycle
            δ.bumpedHalfRight
      = δ_minus_bumpedHalfRight_smoothCycle δ := by
    apply Subtype.ext
    rw [SmoothCycle.coe_sub, SmoothCycle.coe_sub, SmoothCycle.coe_add]
    rw [show (T1_plus_T2_right_chain_smoothCycle δ : SmoothChain I X)
            = SmoothChain.single (SmoothPath.const I X δ.tgt)
              + SmoothChain.single δ
              + SmoothChain.single δ.bumpedHalfRight.reverse
              - SmoothChain.single (SmoothPath.const I X δ.src)
          from rfl,
        single_smoothPath_const_smoothCycle_coe (I := I) (X := X) δ.src,
        single_smoothPath_const_smoothCycle_coe (I := I) (X := X) δ.tgt,
        single_smoothPath_plus_reverse_smoothCycle_coe
          (I := I) (X := X) δ.bumpedHalfRight,
        δ_minus_bumpedHalfRight_smoothCycle_coe δ]
    exact reparam_right_chain_collapse δ
  rw [← h_eq]
  exact h_sum

end JacobianChallenge

end
