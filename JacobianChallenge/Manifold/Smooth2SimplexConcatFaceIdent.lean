/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexFromConcat
import JacobianChallenge.Manifold.SmoothPathBumpedHalf

set_option linter.unusedSectionVars false

/-! # Face identifications for the concat 2-simplex

Identifies `face2` and `face0` of `Smooth2Simplex.ofSmoothPathConcat γ δ h`
with the bumped-half reparameterisations of `γ` and `δ` (respectively).

* `face2_ofSmoothPathConcat_eq` —
  `face2 σ = γ.bumpedHalfLeft`.
* `face0_ofSmoothPathConcat_eq` —
  `face0 σ = δ.bumpedHalfRight`.

Combined with `face1_ofSmoothPathConcat_eq` (which gives
`face1 σ = γ.concat δ h` from `Smooth2SimplexFromConcat.lean`), this
gives the **fully-identified boundary chain**:

```
boundary σ = single (δ.bumpedHalfRight) - single (γ.concat δ h)
              + single (γ.bumpedHalfLeft)
           ∈ stokesBoundaries I X.
```

I.e., **`γ.concat δ h` is homologous (mod stokes-boundaries) to the
formal sum `γ.bumpedHalfLeft + δ.bumpedHalfRight`**.

## What this file ships

* `face2_ofSmoothPathConcat_eq`.
* `face0_ofSmoothPathConcat_eq`.
* `boundary_ofSmoothPathConcat_fully_identified` — the identified
  boundary chain identity.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

variable (γ δ : SmoothPath I X) (h : γ.tgt = δ.src)

/-! ## `face2 σ = γ.bumpedHalfLeft` -/

/-- **face2 of the concat 2-simplex equals `γ.bumpedHalfLeft`.**

Both smooth paths share src = `γ.src`, tgt = `γ.tgt`, and underlying
`toPath` function `t ↦ γ.ambient (concatRepLeft (t.val / 2))`. The
face2 of `σ(x₀, x₁) = γ.concatAmbient δ (x₀/2 + x₁)` at parameter
`(t.val, 0)` reads
`γ.concatAmbient δ (t.val / 2 + 0) = γ.concatAmbient δ (t.val / 2)`,
which equals `γ.ambient (concatRepLeft (t.val / 2))` on `[0, 1/2]`
(the left-half region of `concatAmbient`). -/
lemma face2_ofSmoothPathConcat_eq :
    Smooth2Simplex.face2 (Smooth2Simplex.ofSmoothPathConcat γ δ h)
      = γ.bumpedHalfLeft := by
  apply SmoothPath.ext
  · -- src: face2.src = σ.toFun v0 = concatAmbient(0) = γ.src.
    show γ.concatAmbient δ
        ((Smooth2Simplex.v0 : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.v0 : Fin 2 → ℝ) 1)
      = γ.bumpedHalfLeft.src
    have h_v0_0 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v0_1 : (Smooth2Simplex.v0 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v0_0, h_v0_1, SmoothPath.bumpedHalfLeft_src]
    show γ.concatAmbient δ (0 / 2 + 0) = γ.src
    have h_arg : (0 : ℝ) / 2 + 0 = 0 := by norm_num
    rw [h_arg]
    exact γ.concatAmbient_zero δ
  · -- tgt: face2.tgt = σ.toFun v1 = concatAmbient(1/2) = γ.tgt.
    show γ.concatAmbient δ
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
      = γ.bumpedHalfLeft.tgt
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.bumpedHalfLeft_tgt]
    show γ.concatAmbient δ (1 / 2 + 0) = γ.tgt
    have h_arg : (1 : ℝ) / 2 + 0 = 1/2 := by norm_num
    rw [h_arg]
    -- concatAmbient(1/2) = γ.ambient(concatRepLeft(1/2)) = γ.ambient(1) = γ.tgt.
    have h_mem : (1/2 : ℝ) ∈ Set.Iic (1/2 : ℝ) := by
      rw [Set.mem_Iic]
    have h_eq_left :=
      (SmoothPath.concatAmbient_eqOn_left γ δ) h_mem
    show γ.concatAmbient δ (1/2 : ℝ) = γ.tgt
    rw [h_eq_left]
    show γ.ambient (SmoothPath.concatRepLeft (1/2)) = γ.tgt
    rw [SmoothPath.concatRepLeft_eq_one_of_ge _ (by norm_num : (3:ℝ)/8 ≤ 1/2)]
    exact γ.ambient_one_eq_tgt
  · -- toPath pointwise:
    --   face2(σ).toPath t = σ.toFun (face2Param t.val) = σ(t.val, 0)
    --                    = concatAmbient(t.val/2 + 0) = concatAmbient(t.val/2).
    -- bumpedHalfLeft.toPath t = γ.ambient(concatRepLeft(t.val/2)).
    -- These agree because t.val/2 ∈ [0, 1/2] (left-half region).
    intro t
    show γ.concatAmbient δ
        ((Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1)
      = γ.bumpedHalfLeft.toPath t
    have h_p0 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 0
        = t.val := rfl
    have h_p1 : (Smooth2Simplex.face2Param t.val : Fin 2 → ℝ) 1
        = 0 := rfl
    rw [h_p0, h_p1]
    show γ.concatAmbient δ (t.val / 2 + 0)
      = γ.ambient (SmoothPath.concatRepLeft (t.val / 2))
    have h_arg : t.val / 2 + 0 = t.val / 2 := by ring
    rw [h_arg]
    -- t.val / 2 ∈ [0, 1/2] since t.val ∈ [0, 1].
    have ht := t.property
    have h_le : t.val / 2 ≤ 1/2 := by
      have ht1 : t.val ≤ 1 := ht.2
      linarith
    have h_mem : t.val / 2 ∈ Set.Iic (1/2 : ℝ) := by
      rw [Set.mem_Iic]; exact h_le
    have h_eq_left :=
      (SmoothPath.concatAmbient_eqOn_left γ δ) h_mem
    exact h_eq_left

/-! ## `face0 σ = δ.bumpedHalfRight` -/

/-- **face0 of the concat 2-simplex equals `δ.bumpedHalfRight`.**

Both smooth paths share src = `γ.tgt = δ.src`, tgt = `δ.tgt`, and
underlying `toPath` function
`t ↦ δ.ambient (concatRepRight ((1 + t.val) / 2))`. The face0 of
`σ(x₀, x₁) = γ.concatAmbient δ (x₀/2 + x₁)` at parameter
`(1 - t.val, t.val)` reads
`γ.concatAmbient δ ((1 - t.val) / 2 + t.val) = γ.concatAmbient δ ((1 + t.val) / 2)`,
which equals `δ.ambient (concatRepRight ((1 + t.val) / 2))` on
`[1/2, 1]` (the right-half region of `concatAmbient`). -/
lemma face0_ofSmoothPathConcat_eq :
    Smooth2Simplex.face0 (Smooth2Simplex.ofSmoothPathConcat γ δ h)
      = δ.bumpedHalfRight := by
  apply SmoothPath.ext
  · -- src: face0.src = σ.toFun v1 = concatAmbient(1/2) = γ.tgt = δ.src.
    show γ.concatAmbient δ
        ((Smooth2Simplex.v1 : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.v1 : Fin 2 → ℝ) 1)
      = δ.bumpedHalfRight.src
    have h_v1_0 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 0 = 1 := rfl
    have h_v1_1 : (Smooth2Simplex.v1 : Fin 2 → ℝ) 1 = 0 := rfl
    rw [h_v1_0, h_v1_1, SmoothPath.bumpedHalfRight_src]
    show γ.concatAmbient δ (1 / 2 + 0) = δ.src
    have h_arg : (1 : ℝ) / 2 + 0 = 1/2 := by norm_num
    rw [h_arg]
    have h_mem : (1/2 : ℝ) ∈ Set.Iic (1/2 : ℝ) := by rw [Set.mem_Iic]
    have h_eq_left :=
      (SmoothPath.concatAmbient_eqOn_left γ δ) h_mem
    rw [h_eq_left]
    show γ.ambient (SmoothPath.concatRepLeft (1/2)) = δ.src
    rw [SmoothPath.concatRepLeft_eq_one_of_ge _ (by norm_num : (3:ℝ)/8 ≤ 1/2)]
    rw [γ.ambient_one_eq_tgt]
    exact h
  · -- tgt: face0.tgt = σ.toFun v2 = concatAmbient(1) = δ.tgt.
    show γ.concatAmbient δ
        ((Smooth2Simplex.v2 : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.v2 : Fin 2 → ℝ) 1)
      = δ.bumpedHalfRight.tgt
    have h_v2_0 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 0 = 0 := rfl
    have h_v2_1 : (Smooth2Simplex.v2 : Fin 2 → ℝ) 1 = 1 := rfl
    rw [h_v2_0, h_v2_1, SmoothPath.bumpedHalfRight_tgt]
    show γ.concatAmbient δ (0 / 2 + 1) = δ.tgt
    have h_arg : (0 : ℝ) / 2 + 1 = 1 := by norm_num
    rw [h_arg]
    exact γ.concatAmbient_one δ
  · -- toPath pointwise:
    --   face0(σ).toPath t = σ.toFun (face0Param t.val) = σ(1-t.val, t.val)
    --     = concatAmbient((1-t.val)/2 + t.val) = concatAmbient((1+t.val)/2).
    -- bumpedHalfRight.toPath t = δ.ambient(concatRepRight((1+t.val)/2)).
    -- These agree because (1+t.val)/2 ∈ [1/2, 1] (right-half region).
    intro t
    show γ.concatAmbient δ
        ((Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0 / 2
          + (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1)
      = δ.bumpedHalfRight.toPath t
    have h_p0 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 0
        = 1 - t.val := rfl
    have h_p1 : (Smooth2Simplex.face0Param t.val : Fin 2 → ℝ) 1
        = t.val := rfl
    rw [h_p0, h_p1]
    show γ.concatAmbient δ ((1 - t.val) / 2 + t.val)
      = δ.ambient (SmoothPath.concatRepRight ((1 + t.val) / 2))
    have h_arg : (1 - t.val) / 2 + t.val = (1 + t.val) / 2 := by ring
    rw [h_arg]
    -- (1 + t.val) / 2 ∈ [1/2, 1] since t.val ∈ [0, 1].
    have ht := t.property
    rcases eq_or_lt_of_le ht.1 with h_zero | h_pos
    · -- t.val = 0: argument = 1/2, in the middle flat zone where both
      -- formulas evaluate identically.
      have h_t_eq : t.val = 0 := h_zero.symm
      rw [h_t_eq]
      have h_arg2 : (1 + (0 : ℝ)) / 2 = 1/2 := by norm_num
      rw [h_arg2]
      -- concatAmbient(1/2) via left rule equals γ.ambient(concatRepLeft(1/2)) = γ.tgt.
      have h_mem_l : (1/2 : ℝ) ∈ Set.Iic (1/2 : ℝ) := by rw [Set.mem_Iic]
      have h_eq_left :=
        (SmoothPath.concatAmbient_eqOn_left γ δ) h_mem_l
      rw [h_eq_left]
      show γ.ambient (SmoothPath.concatRepLeft (1/2))
        = δ.ambient (SmoothPath.concatRepRight (1/2))
      rw [SmoothPath.concatRepLeft_eq_one_of_ge _ (by norm_num : (3:ℝ)/8 ≤ 1/2)]
      rw [γ.ambient_one_eq_tgt]
      -- δ.ambient(concatRepRight(1/2)) = δ.ambient(0) = δ.src = γ.tgt.
      rw [SmoothPath.concatRepRight_eq_zero_of_le _ (by norm_num : (1/2 : ℝ) ≤ 5/8)]
      rw [δ.ambient_zero_eq_src]
      exact h
    · -- t.val > 0: argument > 1/2, in the right-half region.
      have h_gt : (1 + t.val) / 2 > 1/2 := by linarith
      have h_mem_r : (1 + t.val) / 2 ∈ Set.Ioi (1/2 : ℝ) := by
        rw [Set.mem_Ioi]; exact h_gt
      have h_eq_right :=
        (SmoothPath.concatAmbient_eqOn_right γ δ) h_mem_r
      exact h_eq_right

/-! ## Fully-identified boundary chain identity -/

/-- **Boundary identity from the concat 2-simplex, with all three
faces identified.** -/
theorem boundary_ofSmoothPathConcat_fully_identified :
    Smooth2Simplex.boundary (Smooth2Simplex.ofSmoothPathConcat γ δ h)
      = SmoothChain.single δ.bumpedHalfRight
        - SmoothChain.single (γ.concat δ h)
        + SmoothChain.single γ.bumpedHalfLeft := by
  unfold Smooth2Simplex.boundary
  rw [face0_ofSmoothPathConcat_eq, face1_ofSmoothPathConcat_eq,
      face2_ofSmoothPathConcat_eq]

/-! ## SmoothCycle and stokesBoundary membership -/

/-- **`single δ.bumpedHalfRight - single (γ.concat δ h) + single γ.bumpedHalfLeft`
is a smooth 1-cycle.** -/
lemma fully_identified_chain_concat_mem_smoothCycle :
    SmoothChain.single δ.bumpedHalfRight
      - SmoothChain.single (γ.concat δ h)
      + SmoothChain.single γ.bumpedHalfLeft
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [← boundary_ofSmoothPathConcat_fully_identified]
  rw [SmoothCycle.mem_iff]
  have h_eq :
      Smooth2Chain.boundary₂
        (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathConcat γ δ h))
      = Smooth2Simplex.boundary (Smooth2Simplex.ofSmoothPathConcat γ δ h) :=
    Smooth2Chain.boundary₂_single _
  rw [← h_eq]
  exact Smooth2Chain.boundary_boundary₂ _

/-- **Packaged SmoothCycle with fully-identified faces.** -/
noncomputable def fully_identified_chain_concat_smoothCycle :
    SmoothCycle I X :=
  ⟨SmoothChain.single δ.bumpedHalfRight
    - SmoothChain.single (γ.concat δ h)
    + SmoothChain.single γ.bumpedHalfLeft,
    fully_identified_chain_concat_mem_smoothCycle γ δ h⟩

/-- **The fully-identified concat boundary cycle lies in
`stokesBoundaries`.** -/
theorem fully_identified_chain_concat_smoothCycle_mem_stokesBoundaries :
    fully_identified_chain_concat_smoothCycle γ δ h
      ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofSmoothPathConcat γ δ h), ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathConcat γ δ h)) :
        SmoothChain I X)
      = SmoothChain.single δ.bumpedHalfRight
        - SmoothChain.single (γ.concat δ h)
        + SmoothChain.single γ.bumpedHalfLeft
  rw [Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂_single]
  exact boundary_ofSmoothPathConcat_fully_identified γ δ h

end JacobianChallenge

end
