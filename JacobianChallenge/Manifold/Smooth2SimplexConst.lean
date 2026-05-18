/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2ChainStokesBoundary

set_option linter.unusedSectionVars false

/-! # The constant smooth 2-simplex

The degenerate smooth 2-simplex `Smooth2Simplex.const I X P` is the
constant map `(Fin 2 → ℝ) → X` at a point `P : X`. Its boundary as a
`SmoothChain` is `single (face₀) - single (face₁) + single (face₂)`
where each face is a "constant" smooth path at `P`.

Without proving the face-equality lemmas
`face_i (const) = face_j (const)` (which would require structural
extensionality between SmoothPaths with definitionally-equal but
syntactically-distinct `src`/`tgt` types), we still get a clean
result: `boundary (const P)` IS a smooth 1-cycle (by `d² = 0`), and
it is the boundary of a single 2-chain. Hence it lies in
`stokesBoundaries I X`.

This is the foundational lemma for ultimately proving that
constant-path-style cycles are smooth 2-chain boundaries — the first
step toward `H₁(X; ℤ) = 0` at genus 0 via simply-connectedness.

## What this file ships

* `Smooth2Simplex.const I X P` — the constant 2-simplex at `P : X`.
* `boundary_const_smoothCycle P` — `Smooth2Simplex.boundary (const P)`
  packaged as a `SmoothCycle I X` via `d² = 0`.
* `boundary_const_smoothCycle_mem_stokesBoundaries` — that cycle lies
  in `stokesBoundaries I X` via the explicit witness
  `Smooth2Chain.single (const P)`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace JacobianChallenge

namespace Smooth2Simplex

/-- **The constant smooth 2-simplex at a point.** Has constant
underlying map `(fun _ => P)`, with `contMDiff_const` as the
smoothness witness. -/
noncomputable def const (P : X) : Smooth2Simplex I X where
  toFun := fun _ => P
  smooth := contMDiff_const

variable {I X}

@[simp] lemma const_toFun (P : X) (x : Fin 2 → ℝ) :
    (Smooth2Simplex.const I X P).toFun x = P := rfl

end Smooth2Simplex

/-- **`Smooth2Simplex.boundary (const P)` packaged as a `SmoothCycle`.**
Boundary of a 2-simplex is always a cycle (by `d² = 0`), so the
constant-simplex case is no exception. -/
noncomputable def boundary_const_smoothCycle (P : X) : SmoothCycle I X :=
  ⟨Smooth2Simplex.boundary (Smooth2Simplex.const I X P), by
    -- `d² = 0`: boundary of a 2-simplex boundary is zero.
    rw [SmoothCycle.mem_iff]
    -- Apply the `d² = 0` identity `boundary ∘ boundary₂Cycle = 0`
    -- specialized to a single 2-simplex.
    have h_boundary₂_single :
        Smooth2Chain.boundary₂ (Smooth2Chain.single (Smooth2Simplex.const I X P))
          = Smooth2Simplex.boundary (Smooth2Simplex.const I X P) :=
      Smooth2Chain.boundary₂_single _
    rw [← h_boundary₂_single]
    exact Smooth2Chain.boundary_boundary₂ _⟩

@[simp] lemma boundary_const_smoothCycle_coe (P : X) :
    (boundary_const_smoothCycle (I := I) (X := X) P : SmoothChain I X)
      = Smooth2Simplex.boundary (Smooth2Simplex.const I X P) := rfl

/-- **`boundary_const_smoothCycle P` lies in `stokesBoundaries I X`.**
Direct application of `mem_stokesBoundaries_iff` with the explicit
witness `Smooth2Chain.single (const P)`. -/
theorem boundary_const_smoothCycle_mem_stokesBoundaries (P : X) :
    boundary_const_smoothCycle (I := I) (X := X) P ∈ stokesBoundaries I X := by
  refine (mem_stokesBoundaries_iff (I := I) (X := X)).mpr ?_
  refine ⟨Smooth2Chain.single (Smooth2Simplex.const I X P), ?_⟩
  apply Subtype.ext
  show (Smooth2Chain.boundary₂Cycle
          (Smooth2Chain.single (Smooth2Simplex.const I X P)) :
        SmoothChain I X)
      = Smooth2Simplex.boundary (Smooth2Simplex.const I X P)
  rw [Smooth2Chain.boundary₂Cycle_coe]
  exact Smooth2Chain.boundary₂_single _

end JacobianChallenge

end
