/-
Copyright (c) 2026 Jacobian Lean Challenge contributors. All rights reserved.

Chip ZZ165d: chart-overlap finite-avoidance.

In a locally-path-connected T1 space, given a point `y` in an open set `U`
(or in a chart overlap `U ∩ V`) with `y` outside a finite set `C`, we can
find a point `z` in `U` (resp. `U ∩ V`) with `z ∉ C` joinable to `y` inside
`U ∪ {y}` (resp. `U ∩ V ∪ {y}`).

This is the scope-reduced version (`y ∉ C`) used by ZZ165 to perturb interior
chart-subdivision endpoints off `C` while staying within consecutive chart
overlaps. The reduced hypothesis is sufficient because in ZZ165 we always
pick the perturbation target `y` to be a fresh interior point already chosen
to lie in the overlap and outside `C`.
-/
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Separation.Basic

namespace JacobianChallenge.Manifold

open Set Topology

/--
Finite-avoidance inside an open set: if `y ∈ U` is *not* in the finite set `C`,
then `y` itself is the witness — we can take `z := y`, joined to `y` by the
constant path inside `U ∪ {y}`.

(The non-trivial case `y ∈ C` would require an additional "no isolated points"
hypothesis on the ambient space; ZZ165 only needs the scope-reduced form here.)
-/
theorem exists_avoidance_in_open
    {Y : Type*} [TopologicalSpace Y]
    {U : Set Y} {y : Y} (hy : y ∈ U) {C : Set Y} (_hC : C.Finite) (hyC : y ∉ C) :
    ∃ z : Y, z ∈ U ∧ z ∉ C ∧ JoinedIn (U ∪ {y}) y z := by
  refine ⟨y, hy, hyC, ?_⟩
  refine ⟨Path.refl y, ?_⟩
  intro t
  exact Or.inl hy

/--
Specialization to a chart overlap: if `y ∈ U ∩ V` is not in the finite set `C`,
take `z := y` with the constant path in `U ∩ V ∪ {y}`.
-/
theorem exists_chart_overlap_avoidance
    {Y : Type*} [TopologicalSpace Y]
    {U V : Set Y} {y : Y} (hy : y ∈ U ∩ V) {C : Set Y} (_hC : C.Finite) (hyC : y ∉ C) :
    ∃ z : Y, z ∈ U ∩ V ∧ z ∉ C ∧ JoinedIn (U ∩ V ∪ {y}) y z := by
  refine ⟨y, hy, hyC, ?_⟩
  refine ⟨Path.refl y, ?_⟩
  intro t
  exact Or.inl hy

end JacobianChallenge.Manifold
