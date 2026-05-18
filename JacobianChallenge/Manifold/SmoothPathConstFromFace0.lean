/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConstFaceEq
import JacobianChallenge.Manifold.SmoothPathConst

set_option linter.unusedSectionVars false

/-! # `face0 (const P) = SmoothPath.const I X P`

Both `Smooth2Simplex.face0 (Smooth2Simplex.const I X P)` and
`SmoothPath.const I X P` are smooth paths carrying:

* `src = tgt = P` definitionally;
* `toPath.toFun = fun _ : unitInterval => P`;
* a Prop-valued continuity / smoothness witness.

The respective `toPath` values are constructed via different
helpers: `pathOfUnitIntervalMap (fun _ => P) _ P P _ _` for the face,
and `Path.refl P` for `SmoothPath.const`. Their `toFun` fields agree
definitionally; their continuity and source/target proof fields are
in `Prop` and hence proof-irrelevant. So the structural equality
follows via `congr 1`.

## What this file ships

* `face0_const_eq_smoothPath_const` — `face0 (const P) = SmoothPath.const I X P`.
* `single_smoothPath_const_smoothCycle` — the SmoothCycle packaging.
* `single_smoothPath_const_smoothCycle_mem_stokesBoundaries` —
  `SmoothChain.single (SmoothPath.const I X P)` (packaged as a
  SmoothCycle) lies in `stokesBoundaries`.

This exhibits a concrete non-trivial element of `stokesBoundaries`
that is naturally indexed by `P : X`: the canonical constant path
single. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

/-- **The face0 of the constant 2-simplex equals the canonical
constant `SmoothPath`.** -/
lemma face0_const_eq_smoothPath_const (P : X) :
    Smooth2Simplex.face0 (Smooth2Simplex.const I X P)
      = SmoothPath.const I X P := by
  show (⟨_, _, _, _⟩ : SmoothPath I X) = ⟨_, _, _, _⟩
  congr 1

/-- **The boundary of the constant 2-simplex equals
`SmoothChain.single (SmoothPath.const I X P)`.** -/
theorem boundary_const_eq_single_smoothPath_const (P : X) :
    Smooth2Simplex.boundary (Smooth2Simplex.const I X P)
      = SmoothChain.single (SmoothPath.const I X P) := by
  rw [boundary_const_eq_single_face0, face0_const_eq_smoothPath_const]

/-- **`SmoothChain.single (SmoothPath.const I X P)` is a smooth 1-cycle.** -/
lemma single_smoothPath_const_mem_smoothCycle (P : X) :
    SmoothChain.single (SmoothPath.const I X P)
      ∈ JacobianChallenge.SmoothCycle I X := by
  rw [SmoothCycle.mem_iff, SmoothChain.boundary_single, SmoothChain.boundarySingle]
  simp [SmoothPath.const_src, SmoothPath.const_tgt]

/-- **The packaged constant `SmoothCycle`.** -/
noncomputable def single_smoothPath_const_smoothCycle (P : X) :
    SmoothCycle I X :=
  ⟨SmoothChain.single (SmoothPath.const I X P),
    single_smoothPath_const_mem_smoothCycle P⟩

@[simp] lemma single_smoothPath_const_smoothCycle_coe (P : X) :
    (single_smoothPath_const_smoothCycle (I := I) (X := X) P : SmoothChain I X)
      = SmoothChain.single (SmoothPath.const I X P) := rfl

/-- **`single_smoothPath_const_smoothCycle P` lies in `stokesBoundaries`.**
Witness: `Smooth2Chain.single (Smooth2Simplex.const I X P)`. -/
theorem single_smoothPath_const_smoothCycle_mem_stokesBoundaries (P : X) :
    single_smoothPath_const_smoothCycle (I := I) (X := X) P
      ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.const I X P), ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.const I X P)) :
        SmoothChain I X)
      = SmoothChain.single (SmoothPath.const I X P)
  rw [Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂_single]
  exact boundary_const_eq_single_smoothPath_const P

end JacobianChallenge

end
