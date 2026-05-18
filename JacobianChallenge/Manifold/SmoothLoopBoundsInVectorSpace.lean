/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexLoopBoundsVectorSpaceT2
import JacobianChallenge.Manifold.BasedSmoothLoopsBound
import JacobianChallenge.Manifold.SmoothPathConstFromFace0

set_option linter.unusedSectionVars false

/-! # Smooth loops in a normed vector space bound

**Headline.** For any normed ℝ-vector space `V` and any smooth loop
`γ : SmoothPath 𝓘(ℝ, V) V` (i.e., `γ.src = γ.tgt`),

```
single_smoothLoop_smoothCycle γ h_loop ∈ stokesBoundaries 𝓘(ℝ, V) V.
```

I.e., **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) V p₀` holds**
unconditionally for any basepoint `p₀ : V` (since every loop at any
point bounds via the linear-contraction 2-chain).

## Proof

Sum the boundary of T₁ + T₂ (the two-triangle decomposition of the
homotopy square from γ to the constant path at γ.src):

```
∂T₁ = const γ.src - diagonal + γ.
∂T₂ = const γ.src - const γ.src + diagonal = diagonal.
∂(T₁ + T₂) = const γ.src + γ.
```

So `single (const γ.src) + single γ ∈ stokesBoundaries`. Combined with
`single (const γ.src) ∈ stokesBoundaries` (const-membership), this
gives `single γ ∈ stokesBoundaries`.

## What this file ships

* `boundary_loopBound_T1_plus_T2_eq` — the boundary chain identity.
* `loopBound_T1_plus_T2_smoothCycle_mem_stokesBoundaries` — the full
  2-chain boundary cycle lies in `stokesBoundaries`.
* `single_smoothLoop_in_stokesBoundaries_vectorSpace` — the headline:
  `single γ ∈ stokesBoundaries` for any smooth loop `γ` in `V`.
* `basedSmoothLoopsBoundHypothesis_vectorSpace` — discharges the
  `BasedSmoothLoopsBoundHypothesis` predicate unconditionally on `V`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace JacobianChallenge

variable (γ : SmoothPath 𝓘(ℝ, V) V)

/-! ## Boundary identity for T₁ + T₂ -/

theorem boundary_loopBound_T1_plus_T2_eq (h_loop : γ.src = γ.tgt) :
    Smooth2Chain.boundary₂
        (Smooth2Chain.single (Smooth2Simplex.ofLoopBoundT1 γ)
          + Smooth2Chain.single (Smooth2Simplex.ofLoopBoundT2 γ))
      = SmoothChain.single (SmoothPath.const 𝓘(ℝ, V) V γ.src)
        + SmoothChain.single γ := by
  rw [map_add]
  rw [Smooth2Chain.boundary₂_single, Smooth2Chain.boundary₂_single]
  unfold Smooth2Simplex.boundary
  rw [face0_ofLoopBoundT1_eq_const_src γ h_loop,
      face2_ofLoopBoundT1_eq γ,
      face0_ofLoopBoundT2_eq_const_src γ,
      face1_ofLoopBoundT2_eq_const_src γ,
      face2_ofLoopBoundT2_eq_face1_ofLoopBoundT1 γ]
  -- (single (const γ.src) - single (face1 T₁) + single γ)
  --   + (single (const γ.src) - single (const γ.src) + single (face1 T₁))
  -- = single (const γ.src) + single γ.
  abel

/-! ## SmoothCycle and stokesBoundaries membership for `single (const γ.src) + single γ` -/

lemma loopBound_T1_plus_T2_chain_mem_smoothCycle (h_loop : γ.src = γ.tgt) :
    SmoothChain.single (SmoothPath.const 𝓘(ℝ, V) V γ.src)
      + SmoothChain.single γ
      ∈ JacobianChallenge.SmoothCycle 𝓘(ℝ, V) V := by
  rw [← boundary_loopBound_T1_plus_T2_eq γ h_loop]
  rw [SmoothCycle.mem_iff]
  exact Smooth2Chain.boundary_boundary₂ _

noncomputable def loopBound_T1_plus_T2_smoothCycle
    (h_loop : γ.src = γ.tgt) :
    SmoothCycle 𝓘(ℝ, V) V :=
  ⟨SmoothChain.single (SmoothPath.const 𝓘(ℝ, V) V γ.src)
    + SmoothChain.single γ,
    loopBound_T1_plus_T2_chain_mem_smoothCycle γ h_loop⟩

theorem loopBound_T1_plus_T2_smoothCycle_mem_stokesBoundaries
    (h_loop : γ.src = γ.tgt) :
    loopBound_T1_plus_T2_smoothCycle γ h_loop
      ∈ stokesBoundaries 𝓘(ℝ, V) V := by
  refine (mem_stokesBoundaries_iff (I := 𝓘(ℝ, V)) (X := V)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofLoopBoundT1 γ)
            + Smooth2Chain.single (Smooth2Simplex.ofLoopBoundT2 γ), ?_⟩
  apply Subtype.ext
  show ((Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofLoopBoundT1 γ)
            + Smooth2Chain.single (Smooth2Simplex.ofLoopBoundT2 γ)) :
          SmoothCycle 𝓘(ℝ, V) V) : SmoothChain 𝓘(ℝ, V) V)
      = _
  rw [Smooth2Chain.boundary₂Cycle_coe]
  exact boundary_loopBound_T1_plus_T2_eq γ h_loop

/-! ## Chain-level collapse -/

private lemma single_loop_chain_collapse :
    (SmoothChain.single (SmoothPath.const 𝓘(ℝ, V) V γ.src)
      + SmoothChain.single γ)
      - SmoothChain.single (SmoothPath.const 𝓘(ℝ, V) V γ.src)
      = SmoothChain.single γ := by
  abel

/-! ## Headline -/

/-- **Every smooth loop in a normed vector space `V` is in
`stokesBoundaries`.**

Proof: subtract `single (const γ.src) ∈ stokesBoundaries` (const-membership)
from `single (const γ.src) + single γ ∈ stokesBoundaries`
(via T₁+T₂ boundary). -/
theorem single_smoothLoop_in_stokesBoundaries_vectorSpace
    (h_loop : γ.src = γ.tgt) :
    single_smoothLoop_smoothCycle γ h_loop ∈ stokesBoundaries 𝓘(ℝ, V) V := by
  have h_combined :=
    loopBound_T1_plus_T2_smoothCycle_mem_stokesBoundaries γ h_loop
  have h_const :=
    JacobianChallenge.single_smoothPath_const_smoothCycle_mem_stokesBoundaries
      (I := 𝓘(ℝ, V)) (X := V) γ.src
  have h_sub : loopBound_T1_plus_T2_smoothCycle γ h_loop
      - JacobianChallenge.single_smoothPath_const_smoothCycle γ.src
      ∈ stokesBoundaries 𝓘(ℝ, V) V :=
    AddSubgroup.sub_mem _ h_combined h_const
  -- Show the cycle-level equality.
  have h_eq :
      loopBound_T1_plus_T2_smoothCycle γ h_loop
        - JacobianChallenge.single_smoothPath_const_smoothCycle γ.src
      = single_smoothLoop_smoothCycle γ h_loop := by
    apply Subtype.ext
    rw [SmoothCycle.coe_sub]
    rw [show (loopBound_T1_plus_T2_smoothCycle γ h_loop : SmoothChain 𝓘(ℝ, V) V)
            = SmoothChain.single (SmoothPath.const 𝓘(ℝ, V) V γ.src)
              + SmoothChain.single γ from rfl,
        single_smoothPath_const_smoothCycle_coe (I := 𝓘(ℝ, V)) (X := V) γ.src,
        single_smoothLoop_smoothCycle_coe γ h_loop]
    exact single_loop_chain_collapse γ
  rw [← h_eq]
  exact h_sub

/-! ## Discharge of `BasedSmoothLoopsBoundHypothesis` on a vector space -/

/-- **`BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) V p₀` holds for any
`p₀ : V`.** Every smooth loop based at any point of `V` bounds a
smooth 2-chain. -/
theorem basedSmoothLoopsBoundHypothesis_vectorSpace (p₀ : V) :
    BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, V) V p₀ := by
  intro γ h_src h_tgt
  exact single_smoothLoop_in_stokesBoundaries_vectorSpace γ
    (h_src.trans h_tgt.symm)

end JacobianChallenge

end
