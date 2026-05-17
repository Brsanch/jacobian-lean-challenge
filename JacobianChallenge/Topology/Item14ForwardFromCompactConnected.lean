/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14ForwardFromFiniteDim
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.style.longLine false

/-! # Item 14 forward direction with `[FiniteDimensional]` dropped

The `Item14ForwardFromFiniteDim` chip discharges the forward direction
of item 14 from `[FiniteDimensional ℂ (HolomorphicOneForm X)]` plus
`ExistsSimplePoleGermAtSomePoint X` (and, for the bundled biconditional,
`S2ImpliesGenus0 X`).

Item 1 became STRICT-CLOSED on 2026-05-17 via the Forster density-bound +
Riesz finale arc — `holomorphicOneFormFiniteDim_holds` makes
`HolomorphicOneFormFiniteDim X` (≡ `Module.Finite ℂ (HolomorphicOneForm
X)`) unconditional on compact connected complex 1-manifolds. So
`[FiniteDimensional]` is no longer a separate hypothesis: it is
synthesisable from the manifold typeclass arguments already present.

This file lifts each theorem of `Item14ForwardFromFiniteDim` to a variant
that drops the `[FiniteDimensional]` typeclass, replacing it with the
internal derivation through `holomorphicOneFormFiniteDim_holds`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Forward discharge with `[FiniteDimensional]` dropped.** Combines
`genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim` with the
unconditional `holomorphicOneFormFiniteDim_holds`. The
`ExistsSimplePoleGermAtSomePoint X` input is the only remaining
hypothesis. -/
theorem genus0ImpliesS2_from_existsSimplePoleGerm
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X) :
    Genus0ImpliesS2 X := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    finiteDimensional_of_HolomorphicOneFormFiniteDim
      (DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X))
  exact genus0ImpliesS2_from_existsSimplePoleGerm_and_finiteDim X hSP

/-- **Bundle assembly with `[FiniteDimensional]` dropped.** -/
theorem surfaceClassificationGenus_from_existsSimplePoleGerm
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (hS2 : S2ImpliesGenus0 X) :
    SurfaceClassificationGenus X where
  genus_zero_to_sphere :=
    genus0ImpliesS2_from_existsSimplePoleGerm X hSP
  sphere_to_genus_zero := hS2

/-- **Item 14 biconditional with `[FiniteDimensional]` dropped.** The
forward direction only needs `ExistsSimplePoleGermAtSomePoint X`; the
reverse direction needs `S2ImpliesGenus0 X`. -/
theorem genus_eq_zero_iff_homeo_from_existsSimplePoleGerm
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (hS2 : S2ImpliesGenus0 X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  (surfaceClassificationGenus_from_existsSimplePoleGerm X hSP hS2).toIff

end JacobianChallenge

end
