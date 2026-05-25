/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.EtalePrimitivesIsLocalHomeomorph
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex

set_option linter.unusedSectionVars false

/-! # Étale-space covering-map infrastructure (Chip 4a)

Foundational instances/lemmas for upgrading
`isLocalHomeomorph_proj : IsLocalHomeomorph (proj om)` (Chip 3) to a
covering map and applying mathlib's monodromy/lifting theorems.

## What this file ships

* `chartedSpaceComplex_locPathConnectedSpace : LocPathConnectedSpace X`
  — `X` is locally path-connected because `ℂ` is and `X` is modelled on
  `ℂ`. Specialisation of `ChartedSpace.locPathConnectedSpace` with
  `LocPathConnectedSpace ℂ` from the
  `LocallyConvexSpace.toLocPathConnectedSpace` instance for ℝ-modules.

* `basicSheet_inter_fiber_eq_singleton` — the basic sheet at
  `(x, (convexBallChartAt x).source, c)` intersects the fiber
  `proj om ⁻¹' {x}` in exactly `{⟨x, c⟩}`. The combinatorial core of
  fiber discreteness.

* `discreteTopology_proj_preimage_singleton : DiscreteTopology (proj om ⁻¹' {x})`
  — each fiber of the étale projection is a discrete subspace.

These two ingredients feed Chip 4b (trivializing homeomorphism +
`IsCoveringMap (proj om)`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set

namespace JacobianChallenge

namespace EtalePrimitives

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  {om : HolomorphicOneForm X}

/-! ## Local path-connectedness of `X` -/

/-- **`X` is locally path-connected.** `X` is modelled on `ℂ` via
`ChartedSpace ℂ X`, and `ℂ` is locally path-connected (as a topological
ℝ-vector space, hence locally convex, hence locally path-connected via
`LocallyConvexSpace.toLocPathConnectedSpace`). Apply
`ChartedSpace.locPathConnectedSpace`. -/
theorem chartedSpaceComplex_locPathConnectedSpace :
    LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace ℂ X

/-! ## Discrete fiber of `proj om` -/

/-- **Combinatorial core of fiber discreteness.** The basic sheet at
`(x, (convexBallChartAt x).source, c)` intersects the fiber
`proj om ⁻¹' {x}` in exactly the singleton `{⟨x, c⟩}`.

Forward direction: an element of the intersection has `point = x` (fiber
membership), and `primValue = chartLocalPrimitiveMax(x) x x + c = 0 + c = c`
(basic-sheet primValue formula + `chartLocalPrimitiveMax_self`). So it
equals `⟨x, c⟩`.

Reverse direction: `⟨x, c⟩` is in the sheet by `self_mem_basicSheet` and
in the fiber by definition. -/
lemma basicSheet_inter_fiber_eq_singleton
    (om : HolomorphicOneForm X) (x : X) (c : ℂ) :
    (basicSheet om x (convexBallChartAt x).source (subset_refl _) c)
        ∩ (proj om ⁻¹' {x})
      = {(⟨x, c⟩ : EtalePrimitives om)} := by
  ext e
  refine ⟨?_, ?_⟩
  · rintro ⟨he_sheet, he_fiber⟩
    -- Fiber membership: e.point = x. Substitute to align basepoint.
    have he_point : e.point = x := he_fiber
    obtain rfl : x = e.point := he_point.symm
    -- Basic-sheet primValue formula at chart-ball-center y = e.point.
    have h_primValue := basicSheet_primValue_eq om e.point _ _ _ he_sheet
    -- Apply chartLocalPrimitiveMax_self (basepoint == evaluation point).
    rw [chartLocalPrimitiveMax_self, zero_add] at h_primValue
    -- Conclude e = ⟨e.point, c⟩.
    have h_eq : e = (⟨e.point, c⟩ : EtalePrimitives om) :=
      EtalePrimitives.ext rfl h_primValue
    rw [h_eq]; rfl
  · intro he
    rw [Set.mem_singleton_iff] at he
    subst he
    refine ⟨?_, rfl⟩
    -- ⟨x, c⟩ ∈ basicSheet at (x, source, c): self-membership.
    exact self_mem_basicSheet om x _ (subset_refl _)
      (convexBallChartAt_x_mem_source x) c

/-- **The fiber `proj om ⁻¹' {x}` is a discrete subspace.** Each
singleton `{⟨e, he⟩} : Set (proj om ⁻¹' {x})` is open in the subspace
topology: witnessed by the basic sheet at
`(e.point = x, source, e.primValue)`, whose intersection with the fiber
is exactly `{e}` by `basicSheet_inter_fiber_eq_singleton`. -/
theorem discreteTopology_proj_preimage_singleton
    (om : HolomorphicOneForm X) (x : X) :
    DiscreteTopology (proj om ⁻¹' {x} : Set (EtalePrimitives om)) := by
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨e, he⟩
  -- `he : e ∈ proj om ⁻¹' {x}`, i.e. `e.point = x`.
  have he_point : e.point = x := he
  -- Take `c := e.primValue`; the basic sheet at `(x, source(x), c)` is
  -- the open neighborhood that isolates `e`.
  set c : ℂ := e.primValue with hc_def
  set B : Set (EtalePrimitives om) :=
    basicSheet om x (convexBallChartAt x).source (subset_refl _) c
    with hB_def
  have hB_open : IsOpen B :=
    basicSheet_isOpen om x _ (convexBallChartAt x).open_source
      (subset_refl _) c
  have h_inter : B ∩ (proj om ⁻¹' {x}) = {(⟨x, c⟩ : EtalePrimitives om)} :=
    basicSheet_inter_fiber_eq_singleton om x c
  -- Use the induced-topology characterisation of `IsOpen`.
  rw [isOpen_induced_iff]
  refine ⟨B, hB_open, ?_⟩
  -- Goal: `Subtype.val ⁻¹' B = {⟨e, he⟩}` (as `Set (proj om ⁻¹' {x})`).
  ext ⟨e', he'⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq]
  constructor
  · intro he'_inB
    -- `e' ∈ B ∩ fiber` ⇒ `e' = ⟨x, c⟩` by `h_inter`.
    have h_inB_fiber : e' ∈ B ∩ (proj om ⁻¹' {x}) := ⟨he'_inB, he'⟩
    rw [h_inter, Set.mem_singleton_iff] at h_inB_fiber
    -- `e = ⟨x, c⟩` (since `e.point = x` and `e.primValue = c = ‹c›`).
    have h_e_eq : e = (⟨x, c⟩ : EtalePrimitives om) :=
      EtalePrimitives.ext he_point rfl
    rw [h_inB_fiber, ← h_e_eq]
  · intro h_eq
    -- Goal: `e' ∈ B`. Rewrite `e' = e`, then use `e = ⟨x, c⟩` + `self_mem_basicSheet`.
    rw [h_eq]
    have h_e_eq : e = (⟨x, c⟩ : EtalePrimitives om) :=
      EtalePrimitives.ext he_point rfl
    rw [h_e_eq]
    exact self_mem_basicSheet om x _ (subset_refl _)
      (convexBallChartAt_x_mem_source x) c

end EtalePrimitives

end JacobianChallenge

end
