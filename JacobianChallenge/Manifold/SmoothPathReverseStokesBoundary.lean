/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexFromPath

set_option linter.unusedSectionVars false

/-! # `single γ + single γ.reverse ∈ stokesBoundaries`

Composes the boundary-of-path-2-simplex identity (chip 17) with the
constant-path stokesBoundary membership (chip 15) to conclude that for
any smooth path `γ : SmoothPath I X`, the chain
`SmoothChain.single γ + SmoothChain.single γ.reverse` (packaged as a
SmoothCycle) lies in `stokesBoundaries I X`.

Classical content: a path and its reverse cancel in smooth singular
homology. Equivalently, `[γ] + [γ.reverse] = 0` in
`(StokesBoundaryInvariance.canonical I X).H1`.

## What this file ships

* `single_smoothPath_plus_reverse_mem_smoothCycle` — the chain
  `SmoothChain.single γ + SmoothChain.single γ.reverse` is a smooth
  1-cycle.
* `single_smoothPath_plus_reverse_smoothCycle` — packaged SmoothCycle.
* `single_smoothPath_plus_reverse_mem_stokesBoundaries` — that
  SmoothCycle lies in `stokesBoundaries I X`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **`single γ + single γ.reverse` is a smooth 1-cycle.** Both
individual `single`s have boundaries `δ_{tgt} - δ_{src}` with the
endpoints swapping in the reverse case, so the sum cancels. -/
lemma single_smoothPath_plus_reverse_mem_smoothCycle (γ : SmoothPath I X) :
    SmoothChain.single γ + SmoothChain.single γ.reverse
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_add,
      SmoothChain.boundary_single, SmoothChain.boundary_single,
      SmoothChain.boundarySingle, SmoothChain.boundarySingle]
  simp [SmoothPath.reverse_src, SmoothPath.reverse_tgt]

/-- **Packaged SmoothCycle.** -/
noncomputable def single_smoothPath_plus_reverse_smoothCycle
    (γ : SmoothPath I X) : SmoothCycle I X :=
  ⟨SmoothChain.single γ + SmoothChain.single γ.reverse,
    single_smoothPath_plus_reverse_mem_smoothCycle γ⟩

@[simp] lemma single_smoothPath_plus_reverse_smoothCycle_coe (γ : SmoothPath I X) :
    (single_smoothPath_plus_reverse_smoothCycle (I := I) (X := X) γ
      : SmoothChain I X)
      = SmoothChain.single γ + SmoothChain.single γ.reverse := rfl

/-- **The forward-plus-reverse stokesBoundary identity.** For any
smooth path `γ`, the chain `single γ + single γ.reverse` (as a
SmoothCycle) lies in `stokesBoundaries I X`.

Derivation: from chip 17, the chain
`single γ.reverse - single (const γ.src) + single γ` lies in
stokesBoundaries (it's the boundary of `Smooth2Chain.single
(ofSmoothPathFstProj γ)`). From chip 15, `single (const γ.src)` lies
in stokesBoundaries (it's the boundary of `Smooth2Chain.single
(Smooth2Simplex.const I X γ.src)`). Adding the two witnesses gives a
2-chain whose boundary is `single γ.reverse + single γ`. -/
theorem single_smoothPath_plus_reverse_mem_stokesBoundaries
    (γ : SmoothPath I X) :
    single_smoothPath_plus_reverse_smoothCycle γ ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  -- Witness: sum of the two 2-chains.
  refine ⟨Smooth2Chain.single (Smooth2Simplex.ofSmoothPathFstProj γ)
            + Smooth2Chain.single (Smooth2Simplex.const I X γ.src), ?_⟩
  apply Subtype.ext
  -- Compute the boundary of the sum.
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.ofSmoothPathFstProj γ)
            + Smooth2Chain.single (Smooth2Simplex.const I X γ.src))
          : SmoothChain I X)
      = SmoothChain.single γ + SmoothChain.single γ.reverse
  rw [Smooth2Chain.boundary₂Cycle_coe]
  -- boundary₂ is ℤ-linear, so distributes over +.
  rw [LinearMap.map_add]
  rw [Smooth2Chain.boundary₂_single, Smooth2Chain.boundary₂_single]
  -- Now: boundary (ofSmoothPathFstProj γ) + boundary (const γ.src)
  --   = (single γ.reverse - single (const γ.src) + single γ)
  --     + single (face0 (const γ.src))
  --   = (single γ.reverse - single (const γ.src) + single γ)
  --     + single (SmoothPath.const I X γ.src)
  --   = single γ.reverse + single γ.
  rw [boundary_ofSmoothPathFstProj_eq, boundary_const_eq_single_smoothPath_const]
  abel

end JacobianChallenge

end
