/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.Smooth2Simplex
import JacobianChallenge.Manifold.SmoothCycle

set_option linter.unusedSectionVars false

/-! # Canonical Stokes-boundaries subgroup from `Smooth2Chain.boundary₂`

The `d² = 0` identity from `Smooth2Simplex.lean` says
`SmoothChain.boundary ∘ boundary₂ = 0`. As a consequence,
`boundary₂` factors through `SmoothCycle I X` — every 2-chain
boundary IS automatically a 1-cycle.

This file constructs the factored map

  `boundary₂Cycle : Smooth2Chain I X →+ SmoothCycle I X`

and packages its image as

  `stokesBoundaries I X : AddSubgroup (SmoothCycle I X)` :=
    the canonical Stokes-boundary subgroup, suitable as the
    `boundaries` field of a `StokesBoundaryInvariance` bundle.

## Significance

This is the canonical algebraic answer to "which cycles are Stokes-
boundaries?": exactly the image of the 2-chain boundary operator.
With this in place, a `StokesBoundaryInvariance` instance can be
constructed honestly: the `boundaries` field is `stokesBoundaries`,
and the only remaining classical content is the **integration-side
Stokes' theorem** (`∫_{∂σ} ω = ∫∫_σ dω`), which remains a named
hypothesis at this mathlib pin.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]

namespace Smooth2Chain

/-- Every smooth 2-chain boundary lies in `SmoothCycle I X`. Direct
consequence of `d² = 0`. -/
lemma boundary₂_mem_smoothCycle (c : Smooth2Chain I X) :
    (boundary₂ c : SmoothChain I X) ∈ JacobianChallenge.SmoothCycle I X := by
  rw [JacobianChallenge.SmoothCycle.mem_iff]
  exact boundary_boundary₂ c

/-- **The 2-chain boundary factored through `SmoothCycle`.** A
`ℤ`-linear map `Smooth2Chain I X →ₗ[ℤ] SmoothCycle I X` (the codomain
is the subtype, equipped with its inherited `AddCommGroup` and
`Module ℤ` from the ambient `SmoothChain`). -/
def boundary₂Cycle : Smooth2Chain I X →ₗ[ℤ] JacobianChallenge.SmoothCycle I X where
  toFun c := ⟨boundary₂ c, boundary₂_mem_smoothCycle c⟩
  map_add' c₁ c₂ := by
    -- Subtype equality reduces to equality of the underlying chains;
    -- `boundary₂` is ℤ-linear.
    apply Subtype.ext
    show (boundary₂ (c₁ + c₂) : SmoothChain I X) = _
    rw [map_add]
    rfl
  map_smul' k c := by
    apply Subtype.ext
    show (boundary₂ (k • c) : SmoothChain I X) = _
    rw [map_smul]
    rfl

@[simp] lemma boundary₂Cycle_coe (c : Smooth2Chain I X) :
    ((boundary₂Cycle c : JacobianChallenge.SmoothCycle I X) : SmoothChain I X)
      = boundary₂ c := rfl

@[simp] lemma boundary₂Cycle_zero :
    boundary₂Cycle (0 : Smooth2Chain I X) = 0 := map_zero _

lemma boundary₂Cycle_add (c₁ c₂ : Smooth2Chain I X) :
    boundary₂Cycle (c₁ + c₂) = boundary₂Cycle c₁ + boundary₂Cycle c₂ :=
  map_add _ _ _

lemma boundary₂Cycle_neg (c : Smooth2Chain I X) :
    boundary₂Cycle (-c) = -boundary₂Cycle c :=
  map_neg _ _

end Smooth2Chain

namespace JacobianChallenge

/-- **The canonical Stokes-boundary subgroup of `SmoothCycle I X`.**
Defined as the image of `Smooth2Chain.boundary₂Cycle`.

Geometrically: a smooth 1-cycle is a Stokes-boundary iff it is the
boundary of some smooth 2-chain. -/
def stokesBoundaries (I : ModelWithCorners ℝ E H) (X : Type*)
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X] :
    AddSubgroup (SmoothCycle I X) :=
  (Smooth2Chain.boundary₂Cycle (I := I) (X := X)).range.toAddSubgroup

/-- A cycle is in `stokesBoundaries I X` iff it is the boundary of
some 2-chain. -/
lemma mem_stokesBoundaries_iff {c : SmoothCycle I X} :
    c ∈ stokesBoundaries I X
      ↔ ∃ d : Smooth2Chain I X, Smooth2Chain.boundary₂Cycle d = c := by
  unfold stokesBoundaries
  -- Membership in `LinearMap.range.toAddSubgroup` unfolds to
  -- membership in `LinearMap.range`, i.e. an exists-preimage statement.
  refine ⟨fun hc => ?_, fun ⟨d, hd⟩ => ?_⟩
  · -- `c ∈ range.toAddSubgroup` unfolds to `c ∈ range`.
    rw [Submodule.mem_toAddSubgroup] at hc
    rcases LinearMap.mem_range.mp hc with ⟨d, hd⟩
    exact ⟨d, hd⟩
  · rw [Submodule.mem_toAddSubgroup]
    exact ⟨d, hd⟩

/-- The zero cycle is a Stokes-boundary (boundary of the zero 2-chain). -/
lemma zero_mem_stokesBoundaries :
    (0 : SmoothCycle I X) ∈ stokesBoundaries I X :=
  (stokesBoundaries I X).zero_mem

/-- Stokes-boundaries are closed under addition. -/
lemma add_mem_stokesBoundaries {c₁ c₂ : SmoothCycle I X}
    (h₁ : c₁ ∈ stokesBoundaries I X) (h₂ : c₂ ∈ stokesBoundaries I X) :
    c₁ + c₂ ∈ stokesBoundaries I X :=
  (stokesBoundaries I X).add_mem h₁ h₂

/-- Stokes-boundaries are closed under negation. -/
lemma neg_mem_stokesBoundaries {c : SmoothCycle I X}
    (h : c ∈ stokesBoundaries I X) :
    -c ∈ stokesBoundaries I X :=
  (stokesBoundaries I X).neg_mem h

end JacobianChallenge

end
