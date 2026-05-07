/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Separation.Basic

set_option diagnostics true
set_option diagnostics.threshold 100

/-! # Local-path-connectedness reduction for the finite-puncture
preconnectedness of a connected complex 1-manifold (ZZ159)

For a connected complex 1-manifold `Y` (`T2Space + ConnectedSpace +
ChartedSpace ℂ Y + IsManifold 𝓘(ℂ) ω Y`), the complement of any finite
set `C` is preconnected. This is the standard "go around the puncture"
fact, used in `RegularSubsetPreconnected.lean` (ZZ154) as the parameter
`h_topo`.

## What this file provides

This file lands the **local-path-connectedness side of the reduction**
unconditionally:

1. `LocPathConnectedSpace ℂ` is a mathlib instance via
   `LocallyConvexSpace.toLocPathConnectedSpace`.

2. `LocPathConnectedSpace Y` follows from `ChartedSpace ℂ Y` via
   `ChartedSpace.locPathConnectedSpace ℂ Y`.

3. For T1 + finite `C`, the complement `Cᶜ` is open
   (`Set.Finite.isClosed.isOpen_compl`).

4. Open subsets of a locally path-connected space are themselves
   locally path-connected (`IsOpen.locPathConnectedSpace`), so the
   subtype `↥Cᶜ` is locally path-connected.

5. On a locally path-connected space, `IsPreconnected ↔ IsPathConnected`
   for nonempty sets (`pathConnectedSpace_iff_connectedSpace` plus
   subtype machinery).

These four pieces are unconditional and live in this file as named
theorems consumable by the rest of the project.

## What this file does NOT close

The remaining content of `h_topo` — namely, that `Cᶜ` is *connected*
on a connected complex 1-manifold (equivalently path-connected, by the
reduction above) — requires either of the following two pieces of
classical content not present in mathlib v4.29.0:

* **(M1)** A manifold-version of
  `Set.Countable.isPathConnected_compl_of_one_lt_rank`, asserting that
  on any connected `LocPathConnectedSpace` modelled on a real vector
  space of rank `> 1` (here `ℂ` over `ℝ`), the complement of a finite
  set is path-connected. Mathlib has the vector-space form
  (`Mathlib/Analysis/Normed/Module/Connected.lean`) but no manifold
  lift.

* **(M2)** The local "punctured-ball is path-connected" statement on
  `ℂ`: for any open ball `B(c, r) ⊆ ℂ` and any point `p ∈ B(c, r)`,
  the punctured ball `B(c, r) \ {p}` is path-connected. Mathlib has
  `isPathConnected_ball` and the global
  `isPathConnected_compl_singleton_of_one_lt_rank`, but the
  intersection lemma `B(c,r) \ {p}` is path-connected requires
  combining these and is not stated explicitly.

With (M2), the manifold lift goes by induction on `|C|` using
`IsPreconnected.union'`: at each step pick a small chart-ball
`W ∋ pₖ` in `Cᶜ_{k-1}`, write
`Cᶜ_k = (Cᶜ_{k-1} \ closedBall) ∪ (W \ {pₖ})`, and combine the two
preconnected pieces. Either of (M1) or (M2) is the missing classical
input.

## Pin status

Per the task spec for ZZ159: the unconditional discharge of `h_topo`
is reported as STUCK on the missing mathlib content (M1)/(M2). This
file lands the LP-connected reduction infrastructure for downstream
consumers; the path-deformation step itself remains parameterised in
`RegularSubsetPreconnected.lean`.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace JacobianChallenge
namespace Manifold

universe u

/-! ## Step 1: `ℂ` is locally path-connected (mathlib instance). -/

/-- `ℂ` is locally path-connected. This is a direct mathlib instance
from `LocallyConvexSpace.toLocPathConnectedSpace` applied to
`ℂ`-as-`ℝ`-module. -/
theorem locPathConnectedSpace_complex : LocPathConnectedSpace ℂ :=
  inferInstance

/-! ## Step 2: any space charted on `ℂ` is locally path-connected. -/

/-- A topological space `Y` charted on `ℂ` is locally path-connected.
This is `ChartedSpace.locPathConnectedSpace ℂ Y`, restated under the
project's name conventions for downstream cite-by-name use. -/
theorem locPathConnectedSpace_of_chartedSpace_complex
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    LocPathConnectedSpace Y :=
  ChartedSpace.locPathConnectedSpace ℂ Y

/-! ## Step 3: complement of a finite set in a `T1Space` is open. -/

/-- For any `T1Space Y`, the complement of a finite set is open. -/
theorem isOpen_compl_of_finite
    {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    {C : Set Y} (hC : C.Finite) :
    IsOpen (Cᶜ : Set Y) :=
  hC.isClosed.isOpen_compl

/-! ## Step 4: subtype `↥Cᶜ` is locally path-connected. -/

/-- For `Y` charted on `ℂ` with `T1Space`, the complement subtype of any
finite set is locally path-connected. -/
theorem locPathConnectedSpace_compl_finite
    {Y : Type u} [TopologicalSpace Y] [T1Space Y] [ChartedSpace ℂ Y]
    {C : Set Y} (hC : C.Finite) :
    LocPathConnectedSpace ((Cᶜ : Set Y)) :=
  haveI : LocPathConnectedSpace Y :=
    locPathConnectedSpace_of_chartedSpace_complex (Y := Y)
  (isOpen_compl_of_finite hC).locPathConnectedSpace

/-! ## Step 5: connected ↔ path-connected reduction on the subtype. -/

/-- On a locally-path-connected `Y`, an open subset is preconnected
iff it is path-connected (when nonempty). This is the standard mathlib
bridge `IsOpen.isConnected_iff_isPathConnected` packaged for the open
complement of a finite set. -/
theorem isPreconnected_compl_finite_iff_isPathConnected_or_empty
    {Y : Type u} [TopologicalSpace Y] [T1Space Y] [ChartedSpace ℂ Y]
    {C : Set Y} (hC : C.Finite) :
    IsPreconnected (Cᶜ : Set Y) ↔
      ((Cᶜ : Set Y) = ∅ ∨ IsPathConnected (Cᶜ : Set Y)) := by
  haveI : LocPathConnectedSpace Y :=
    locPathConnectedSpace_of_chartedSpace_complex (Y := Y)
  by_cases h : (Cᶜ : Set Y) = ∅
  · simp [h, IsPreconnected, isPreconnected_empty]
  · refine ⟨fun hpre => ?_, ?_⟩
    · right
      have hne : (Cᶜ : Set Y).Nonempty := nonempty_iff_ne_empty.mpr h
      have hconn : IsConnected (Cᶜ : Set Y) := ⟨hne, hpre⟩
      exact (isOpen_compl_of_finite hC).isConnected_iff_isPathConnected.mp hconn
    · rintro (hempty | hpath)
      · exact (h hempty).elim
      · exact hpath.isPreconnected

/-! ## Reduction-only headline (not the full discharge)

The full headline `IsPreconnected (Cᶜ : Set Y)` for a connected complex
1-manifold remains parameterised in `RegularSubsetPreconnected.lean`.
This file delivers the unconditional reduction: discharging `h_topo`
is equivalent to discharging
`Cᶜ ≠ ∅ → IsPathConnected (Cᶜ : Set Y)` by the equivalence above.

The remaining mathematical content — that on a connected complex
1-manifold a finite set has path-connected complement — is the
manifold lift of `Set.Countable.isPathConnected_compl_of_one_lt_rank`,
not in mathlib at the pin. See the file docstring for the precise
missing-lemma statement.
-/

/-- **Reduction-only headline.** Given the path-connectedness of `Cᶜ`
(the unproven manifold-lift content), preconnectedness follows. The
hypothesis `h_path` is exactly the missing manifold-lift content
identified as (M1) in the file docstring. -/
theorem isPreconnected_compl_finite_of_isPathConnected
    {Y : Type u} [TopologicalSpace Y] [T1Space Y] [ChartedSpace ℂ Y]
    {C : Set Y} (_hC : C.Finite)
    (h_path : (Cᶜ : Set Y).Nonempty → IsPathConnected (Cᶜ : Set Y)) :
    IsPreconnected (Cᶜ : Set Y) := by
  by_cases h : (Cᶜ : Set Y) = ∅
  · simp [h]
  · have hne : (Cᶜ : Set Y).Nonempty := nonempty_iff_ne_empty.mpr h
    exact (h_path hne).isPreconnected

/-- **Convenience composition.** The hypothesis-shape that
`RegularSubsetPreconnected.lean`'s `h_topo` parameter consumes,
expressed as the path-connectedness of complements of finite sets. -/
theorem h_topo_of_h_path
    {Y : Type u} [TopologicalSpace Y] [T1Space Y] [ChartedSpace ℂ Y]
    (h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y)) :
    ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) := by
  intro C hC
  exact isPreconnected_compl_finite_of_isPathConnected hC (h_path C hC)

end Manifold
end JacobianChallenge
