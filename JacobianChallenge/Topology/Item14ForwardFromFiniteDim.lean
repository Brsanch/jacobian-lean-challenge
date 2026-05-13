/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.HTopFromSubsingleton
import JacobianChallenge.Topology.SurfaceClassificationGenus
import JacobianChallenge.Manifold.HolomorphicOneFormLinear

set_option diagnostics.threshold 100
set_option linter.style.longLine false

/-! # Item 14 forward direction from `FiniteDimensional` + simple-pole-germ

The germfield-arc capstone in `Topology/HTopFromSubsingleton.lean`
(commit `2e5cfb4`, 2026-05-13) reduces the biconditional
`genus_eq_zero_iff_homeo` to one classical input
`ExistsSimplePoleGermAtSomePoint X` modulo a structural **typeclass**
`[Subsingleton (HolomorphicOneForm X)]`.

This chip refactors the typeclass requirement to the weaker Hodge-style
finite-dimensionality hypothesis `[FiniteDimensional ℂ (HolomorphicOneForm
X)]`, for the **forward direction** of item 14
(`Genus0ImpliesS2 X`).

## The trade

* Old form: takes `[Subsingleton (HolomorphicOneForm X)]` as a typeclass.
  Strong: directly says `HolomorphicOneForm X` has at most one element.
* New form (this file): takes `[FiniteDimensional ℂ (HolomorphicOneForm
  X)]` as a typeclass. Weaker: only asserts finite-dimensionality. Under
  `genus X = 0` (the LHS of the forward implication), finite-dim +
  `Module.finrank_zero_iff_forall_zero` yields the Subsingleton internally
  via the existing `holomorphicOneForm_subsingleton_of_genus_eq_zero` in
  `Manifold/HolomorphicOneFormLinear.lean`. The full germfield capstone
  then fires.

The point: `FiniteDimensional` is the *single* Hodge-theoretic content
that remains for compact connected Riemann surfaces — already named as
the open hypothesis `JacobianChallenge.HolomorphicOneFormFiniteDim X` in
`Manifold/HodgeFiniteDimensional.lean`. By stating the forward direction
of item 14 against `FiniteDimensional` rather than `Subsingleton`, we
align item 14's forward leg with the *single* named Hodge gap of the
repository.

## Scope

This is the **forward** direction only. The reverse direction
`S2ImpliesGenus0 X` ("`X ≃ₜ S²` ⇒ `genus X = 0`") cannot be discharged
from finite-dim + simple-pole-germ alone: it needs the
topological-vs-geometric genus bridge (Hodge identification of `H¹` with
harmonic forms, plus `H¹(S²; ℝ) = 0`). That bridge remains an open
hypothesis, captured by `S2ImpliesGenus0 X` in
`Topology/SurfaceClassificationGenus.lean`. The bundled biconditional
under `[FiniteDimensional]` + simple-pole-germ + `S2ImpliesGenus0 X` is
also provided here.

## What this file delivers

* `genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim` — the
  `Genus0ImpliesS2 X` named open input is discharged from
  `[FiniteDimensional]` + `ExistsSimplePoleGermAtSomePoint X`. This is
  the substantive content.
* `surfaceClassificationGenus_from_existsSimplePoleGerm_and_finiteDim`
  — full classification bundle from `[FiniteDimensional]` +
  `ExistsSimplePoleGermAtSomePoint X` + `S2ImpliesGenus0 X`.
* `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_finiteDim` —
  the assembled biconditional `genus X = 0 ↔ Nonempty (X ≃ₜ S²)` under
  the three inputs.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Substantive forward discharge.** Under
`[FiniteDimensional ℂ (HolomorphicOneForm X)]` and
`ExistsSimplePoleGermAtSomePoint X`, the open hypothesis
`Genus0ImpliesS2 X` from `SurfaceClassificationGenus` is provable: given
`genus X = 0`, finite-dim gives `Subsingleton (HolomorphicOneForm X)`,
and the germfield-arc capstone delivers a homeomorphism `X ≃ₜ S²`. -/
theorem genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X) :
    Genus0ImpliesS2 X := by
  intro hg
  haveI hSub : Subsingleton (HolomorphicOneForm X) :=
    holomorphicOneForm_subsingleton_of_genus_eq_zero X hg
  exact (MeromorphicFunctionField.genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_subsingleton X hSP).mp hg

/-- **Bundle assembly under `[FiniteDimensional]`.** Combines the
substantive forward discharge with the named reverse hypothesis
`S2ImpliesGenus0 X` to produce a full `SurfaceClassificationGenus X`
bundle. Under `[FiniteDimensional]`, the forward leg becomes a
*derived* fact rather than a separate named input — reducing the
classification's open hypothesis count from two (`Genus0ImpliesS2` +
`S2ImpliesGenus0`) to one (`S2ImpliesGenus0`) plus the standard Hodge
finite-dim input. -/
theorem surfaceClassificationGenus_from_existsSimplePoleGerm_and_finiteDim
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (hS2 : S2ImpliesGenus0 X) :
    SurfaceClassificationGenus X where
  genus_zero_to_sphere :=
    genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim X hSP
  sphere_to_genus_zero := hS2

/-- **Item 14 biconditional under `[FiniteDimensional]` + the two
classical inputs.** Combines this file's forward discharge with the
reverse `S2ImpliesGenus0 X` hypothesis via `SurfaceClassificationGenus`. -/
theorem genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_finiteDim
    [FiniteDimensional ℂ (HolomorphicOneForm X)]
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (hS2 : S2ImpliesGenus0 X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  (surfaceClassificationGenus_from_existsSimplePoleGerm_and_finiteDim X hSP hS2).toIff

end JacobianChallenge

end
