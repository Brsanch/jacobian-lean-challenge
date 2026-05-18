/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2SimplexConst

set_option linter.unusedSectionVars false

/-! # All three faces of the constant 2-simplex are equal

The constant 2-simplex `Smooth2Simplex.const I X P` has all three
faces equal as `SmoothPath` terms, because:

* The src and tgt fields evaluate definitionally to `P` (via the
  constant nature of `(const P).toFun`).
* The `toPath` field's `toFun` is `fun _ : unitInterval => P`
  in all three cases.
* The continuity proof of `Path.toFun` is in `Prop`, hence
  proof-irrelevant.
* The `smooth` field of `SmoothPath` is an existential in `Prop`,
  hence proof-irrelevant.

So the structural equalities follow from definitional unfolding +
`Path.mk` injectivity-up-to-proof-irrelevance.

## What this file ships

* `Smooth2Simplex.face0_const_eq_face1_const` —
  `face0 (const P) = face1 (const P)`.
* `Smooth2Simplex.face0_const_eq_face2_const` —
  `face0 (const P) = face2 (const P)`.
* `Smooth2Simplex.face1_const_eq_face2_const` —
  `face1 (const P) = face2 (const P)`.

Together these reduce the constant 2-simplex's boundary chain
`single (face0) - single (face1) + single (face2)` to a SINGLE
`single γ_const`, exhibiting a specific smooth path
`γ_const := face0 (const P)` whose `single` lies in
`stokesBoundaries`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

namespace Smooth2Simplex

/-- **All three faces of the constant 2-simplex carry the same data.**
We prove this by direct structural equality: src = tgt = P (definitionally),
underlying `toPath.toFun = fun _ => P` (definitionally), continuity
proof is in `Prop` (proof-irrelevant), and the `SmoothPath.smooth`
existential is in `Prop`. -/
lemma face0_const_eq_face1_const (P : X) :
    Smooth2Simplex.face0 (Smooth2Simplex.const I X P)
      = Smooth2Simplex.face1 (Smooth2Simplex.const I X P) := by
  -- Structural equality of SmoothPath:
  -- LHS = { src := P, tgt := P, toPath := <face0 path>, smooth := <face0 proof> }
  -- RHS = { src := P, tgt := P, toPath := <face1 path>, smooth := <face1 proof> }
  -- src/tgt agree definitionally; toPath.toFun = fun _ => P definitionally;
  -- continuity proofs in Prop; smooth field in Prop.
  show (⟨_, _, _, _⟩ : SmoothPath I X) = ⟨_, _, _, _⟩
  congr 1

/-- **face0 and face2 of constant 2-simplex are equal.** -/
lemma face0_const_eq_face2_const (P : X) :
    Smooth2Simplex.face0 (Smooth2Simplex.const I X P)
      = Smooth2Simplex.face2 (Smooth2Simplex.const I X P) := by
  show (⟨_, _, _, _⟩ : SmoothPath I X) = ⟨_, _, _, _⟩
  congr 1

/-- **face1 and face2 of constant 2-simplex are equal.** -/
lemma face1_const_eq_face2_const (P : X) :
    Smooth2Simplex.face1 (Smooth2Simplex.const I X P)
      = Smooth2Simplex.face2 (Smooth2Simplex.const I X P) :=
  (face0_const_eq_face1_const P).symm.trans (face0_const_eq_face2_const P)

end Smooth2Simplex

/-! ## Constant 2-simplex's boundary as `single γ_const` -/

/-- **The constant 2-simplex's boundary chain collapses to a single
copy of `face0 (const P)`.** Direct consequence of the three faces
being equal as `SmoothPath` terms: `single γ - single γ + single γ
= single γ`. -/
theorem boundary_const_eq_single_face0 (P : X) :
    Smooth2Simplex.boundary (Smooth2Simplex.const I X P)
      = SmoothChain.single (Smooth2Simplex.face0 (Smooth2Simplex.const I X P)) := by
  unfold Smooth2Simplex.boundary
  rw [← Smooth2Simplex.face0_const_eq_face1_const,
      ← Smooth2Simplex.face0_const_eq_face2_const]
  abel

/-- **`SmoothChain.single (face0 (const P))` is a smooth 1-cycle.**
Direct consequence of `boundary_const_eq_single_face0` and the fact
that the boundary of any 2-chain is a 1-cycle (`d² = 0`). -/
lemma single_face0_const_mem_smoothCycle (P : X) :
    SmoothChain.single (Smooth2Simplex.face0 (Smooth2Simplex.const I X P))
      ∈ JacobianChallenge.SmoothCycle I X := by
  have h := (boundary_const_smoothCycle (I := I) (X := X) P).property
  rwa [boundary_const_smoothCycle_coe, boundary_const_eq_single_face0] at h

/-- **The packaged `SmoothCycle` whose underlying chain is
`SmoothChain.single (face0 (const P))`.** -/
noncomputable def single_face0_const_smoothCycle (P : X) :
    SmoothCycle I X :=
  ⟨SmoothChain.single (Smooth2Simplex.face0 (Smooth2Simplex.const I X P)),
    single_face0_const_mem_smoothCycle P⟩

@[simp] lemma single_face0_const_smoothCycle_coe (P : X) :
    (single_face0_const_smoothCycle (I := I) (X := X) P : SmoothChain I X)
      = SmoothChain.single
          (Smooth2Simplex.face0 (Smooth2Simplex.const I X P)) := rfl

/-- **`single_face0_const_smoothCycle P` lies in `stokesBoundaries`.**
Same witness `Smooth2Chain.single (const P)` as
`boundary_const_smoothCycle_mem_stokesBoundaries`, with the chain-side
equality given by `boundary_const_eq_single_face0`. -/
theorem single_face0_const_smoothCycle_mem_stokesBoundaries (P : X) :
    single_face0_const_smoothCycle (I := I) (X := X) P
      ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.const I X P), ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.const I X P)) :
        SmoothChain I X)
      = SmoothChain.single
          (Smooth2Simplex.face0 (Smooth2Simplex.const I X P))
  rw [Smooth2Chain.boundary₂Cycle_coe, Smooth2Chain.boundary₂_single]
  exact boundary_const_eq_single_face0 P

end JacobianChallenge

end
