/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusProjFace1UL
import JacobianChallenge.Manifold.SmoothPathConstFromFace0
import JacobianChallenge.Manifold.BasedSmoothLoopsBound

set_option linter.unusedSectionVars false

/-! # Bordism `single γ - single (torusBasisLoop λ) ∈ stokesBoundaries`

Combines the four face identifications from `ComplexTorusProjFaces.lean`
(`face0 σ_LR = torusBasisLoop λ`, `face2 σ_LR = const 0`,
`face0 σ_UL = const 0`, `face2 σ_UL = face1 σ_LR`) with the substantive
identification `face1 σ_UL = γ` (from `ComplexTorusProjFace1UL.lean`).

Summing `∂σ_LR + ∂σ_UL` cancels the diagonal `face1 σ_LR = face2 σ_UL`
and leaves:

```
∂σ_LR = single (torusBasisLoop λ) - single (diag) + single (const 0)
∂σ_UL = single (const 0) - single γ + single (diag)
```

so `∂(σ_LR + σ_UL) = single (torusBasisLoop λ) - single γ + 2·single (const 0)`.

Hence `(γ_λ - γ).singleCycle + 2·const.singleCycle ∈ stokesBoundaries`, and
since `const.singleCycle ∈ stokesBoundaries` (already established), so is
`(γ_λ - γ).singleCycle`, giving by negation:

```
single γ - single (torusBasisLoop λ) ∈ stokesBoundaries.
```

## What this file ships

* `boundary_projLR_plus_projUL_eq` — the boundary identity in
  `SmoothChain`.
* `single_γ_sub_single_torusBasisLoop_mem_stokesBoundaries` — the
  headline bordism.

No `sorry`, no `axiom`. -/

open Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

variable {L}

/-! ## Boundary identity in `SmoothChain` -/

/-- **The boundary chain identity for `σ_LR + σ_UL`.** -/
theorem boundary_projLR_plus_projUL_eq
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift)
    (h_lift_zero : lift 0 = 0) (h_lift_one : lift 1 = lam) (h_lam : lam ∈ L)
    (h_γ_src : γ.src = (0 : ℂ ⧸ L)) (h_γ_tgt : γ.tgt = (0 : ℂ ⧸ L))
    (h_lift_agrees : ∀ t ∈ Set.Icc (0 : ℝ) 1, L.mkQ (lift t) = γ.ambient t) :
    Smooth2Chain.boundary₂
        (Smooth2Chain.single (projLowerRight L lift lam h_lift)
          + Smooth2Chain.single (projUpperLeft L lift lam h_lift))
      = SmoothChain.single (torusBasisLoop lam h_lam)
        - SmoothChain.single γ
        + (2 : ℤ) • SmoothChain.single
            (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)) := by
  rw [map_add]
  rw [Smooth2Chain.boundary₂_single, Smooth2Chain.boundary₂_single]
  unfold Smooth2Simplex.boundary
  rw [face0_projLowerRight_eq_torusBasisLoop lift lam h_lift h_lift_zero h_lift_one h_lam,
      face2_projLowerRight_eq_const lift lam h_lift h_lift_zero,
      face0_projUpperLeft_eq_const lift lam h_lift h_lift_one h_lam,
      face1_projUpperLeft_eq γ lift lam h_lift h_lift_zero h_lift_one h_lam
        h_γ_src h_γ_tgt h_lift_agrees,
      face2_projUpperLeft_eq_face1_projLowerRight lift lam h_lift]
  -- After substitution:
  --  ∂σ_LR = single γ_λ - single (face1 σ_LR) + single const
  --  ∂σ_UL = single const - single γ + single (face1 σ_LR)
  -- Sum = single γ_λ - single γ + 2 · single const.
  -- `(2 : ℤ) • single const = single const + single const`.
  have h_two : (2 : ℤ) • SmoothChain.single
        (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
      = SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
        + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)) :=
    two_zsmul _
  rw [h_two]
  abel

/-! ## Stokes-boundary membership -/

/-- **The headline bordism on `ℂ ⧸ L`.**

For any smooth based loop `γ` at `0` admitting a smooth ambient lift
`lift : ℝ → ℂ` (`lift 0 = 0`, `lift 1 = λ ∈ L`,
`mkQ (lift t) = γ.ambient t` on `[0, 1]`),

```
single γ - single (torusBasisLoop λ) ∈ stokesBoundaries.
```

i.e., `γ` and `torusBasisLoop λ` are smoothly bordant on `T_L`. -/
theorem single_γ_sub_single_torusBasisLoop_mem_stokesBoundaries
    (γ : SmoothPath 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    (lift : ℝ → ℂ) (lam : ℂ)
    (h_lift : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ lift)
    (h_lift_zero : lift 0 = 0) (h_lift_one : lift 1 = lam) (h_lam : lam ∈ L)
    (h_γ_src : γ.src = (0 : ℂ ⧸ L)) (h_γ_tgt : γ.tgt = (0 : ℂ ⧸ L))
    (h_lift_agrees : ∀ t ∈ Set.Icc (0 : ℝ) 1, L.mkQ (lift t) = γ.ambient t) :
    single_smoothLoop_smoothCycle γ (h_γ_src.trans h_γ_tgt.symm)
      - single_smoothLoop_smoothCycle (torusBasisLoop lam h_lam)
          ((torusBasisLoop_src lam h_lam).trans
            (torusBasisLoop_tgt lam h_lam).symm)
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) := by
  -- Step 1: Set the 2-chain c := single σ_LR + single σ_UL.
  set σ_LR := projLowerRight L lift lam h_lift with hσ_LR_def
  set σ_UL := projUpperLeft L lift lam h_lift with hσ_UL_def
  set c : Smooth2Chain 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    Smooth2Chain.single σ_LR + Smooth2Chain.single σ_UL with hc_def
  -- Step 2: boundary₂Cycle c lives in stokesBoundaries by definition.
  have h_in : Smooth2Chain.boundary₂Cycle c ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    (mem_stokesBoundaries_iff (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L)).mpr ⟨c, rfl⟩
  -- Step 3: const.singleCycle ∈ stokesBoundaries.
  have h_const_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L)
          (0 : ℂ ⧸ L)
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    single_smoothPath_const_smoothCycle_mem_stokesBoundaries (0 : ℂ ⧸ L)
  -- Step 4: const.singleCycle + const.singleCycle ∈ stokesBoundaries.
  have h_two_const_in :
      single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L) (0 : ℂ ⧸ L)
          + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L) (0 : ℂ ⧸ L)
        ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    AddSubgroup.add_mem _ h_const_in h_const_in
  -- Step 5: Subtract: boundary₂Cycle c - (const + const) ∈ stokesBoundaries.
  have h_sub_in : Smooth2Chain.boundary₂Cycle c
        - (single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L) (0 : ℂ ⧸ L)
            + single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ)) (X := ℂ ⧸ L) (0 : ℂ ⧸ L))
      ∈ stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L) :=
    AddSubgroup.sub_mem _ h_in h_two_const_in
  -- Step 6: Reverse: -(γ_λ - γ).singleCycle = γ.singleCycle - γ_λ.singleCycle.
  -- We'll show:
  --   boundary₂Cycle c - 2 • const.singleCycle
  --   = (torusBasisLoop λ).singleCycle - γ.singleCycle.
  -- Then negate to get γ.singleCycle - (torusBasisLoop λ).singleCycle ∈ stokesBoundaries.
  -- Abbreviations for clarity.
  set gLam_cycle := single_smoothLoop_smoothCycle (torusBasisLoop lam h_lam)
      ((torusBasisLoop_src lam h_lam).trans (torusBasisLoop_tgt lam h_lam).symm)
    with hgLam_cycle_def
  set gamma_cycle := single_smoothLoop_smoothCycle γ (h_γ_src.trans h_γ_tgt.symm)
    with hgamma_cycle_def_
  set const_cycle := single_smoothPath_const_smoothCycle (I := 𝓘(ℝ, ℂ))
      (X := ℂ ⧸ L) (0 : ℂ ⧸ L)
    with hconst_cycle_def
  -- Step 6 (rewritten): show boundary₂Cycle c - (const + const) = gLam_cycle - gamma_cycle.
  have h_eq : Smooth2Chain.boundary₂Cycle c - (const_cycle + const_cycle)
      = gLam_cycle - gamma_cycle := by
    apply Subtype.ext
    rw [SmoothCycle.coe_sub, Smooth2Chain.boundary₂Cycle_coe,
        SmoothCycle.coe_add]
    show (Smooth2Chain.boundary₂ c : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
          - (SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
            + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)))
        = (gLam_cycle : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
          - (gamma_cycle : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
    rw [hgLam_cycle_def, hgamma_cycle_def_, single_smoothLoop_smoothCycle_coe,
        single_smoothLoop_smoothCycle_coe]
    show (Smooth2Chain.boundary₂ c : SmoothChain 𝓘(ℝ, ℂ) (ℂ ⧸ L))
          - (SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
            + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)))
        = SmoothChain.single (torusBasisLoop lam h_lam) - SmoothChain.single γ
    -- Apply the boundary identity (with the 2 • single const expanded
    -- via two_zsmul).
    have h_bdry := boundary_projLR_plus_projUL_eq γ lift lam h_lift h_lift_zero
      h_lift_one h_lam h_γ_src h_γ_tgt h_lift_agrees
    have h_expand : (2 : ℤ) • SmoothChain.single
          (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
        = SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L))
          + SmoothChain.single (SmoothPath.const 𝓘(ℝ, ℂ) (ℂ ⧸ L) (0 : ℂ ⧸ L)) :=
      two_zsmul _
    rw [h_expand] at h_bdry
    rw [h_bdry]
    abel
  rw [h_eq] at h_sub_in
  -- h_sub_in : gLam_cycle - gamma_cycle ∈ stokesBoundaries.
  -- Negate to get gamma_cycle - gLam_cycle ∈ stokesBoundaries.
  have h_neg_eq : -(gLam_cycle - gamma_cycle) = gamma_cycle - gLam_cycle := by abel
  rw [← h_neg_eq]
  exact (stokesBoundaries 𝓘(ℝ, ℂ) (ℂ ⧸ L)).neg_mem h_sub_in

end ComplexTorus

end JacobianChallenge

end
