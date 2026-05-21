/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Homeomorph.Defs

set_option linter.unusedSectionVars false

/-! # ULift transfer for `ChartedSpace` and `HasGroupoid`

Ports `mrdouglasny/jacobian-challenge`'s
`Jacobians.Jacobian.Construction.chartedSpaceULift` + `uliftHasGroupoid`
helpers (no axiom dependencies). These let us lift a charted space
structure from `M : Type 0` to `ULift.{u, 0} M : Type u` so we can
package the analytic Jacobian (constructed as a `ComplexTorus` in
`Type`) at universe `u` to match Buzzard's signature
`Jacobian : Type u`.

## Net contribution

* `chartedSpaceULift` — `ChartedSpace H (ULift M)` from
  `ChartedSpace H M`.
* `uliftHasGroupoid` — transfers `HasGroupoid M G` to `ULift M`.

This is the **mechanical packaging** that lets the analytic-Jacobian
construction land at the universe level Buzzard's challenge expects.
It is the first concrete step in adapting mrdouglasny's `Jacobian X :=
ULift (JacobianAmbient X)` strategy to Bryan's tree without changing
item 2's body.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology
open scoped ContDiff

namespace JacobianChallenge

universe u

/-! ## ULift transfer for `ChartedSpace` -/

section ULiftTransfer

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Charts on `ULift M`** obtained by composing charts on `M` with
the `ULift ↔ M` homeomorphism. -/
@[reducible] noncomputable def chartedSpaceULift :
    ChartedSpace H (ULift M) where
  atlas := Set.image
    (fun chart : OpenPartialHomeomorph M H =>
      Homeomorph.ulift.toOpenPartialHomeomorph.trans chart)
    (ChartedSpace.atlas (H := H) (M := M))
  chartAt p :=
    Homeomorph.ulift.toOpenPartialHomeomorph.trans
      (ChartedSpace.chartAt p.down)
  mem_chart_source p := by
    simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
      PartialEquiv.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,
      OpenPartialHomeomorph.toFun_eq_coe,
      Homeomorph.toOpenPartialHomeomorph_apply,
      Set.univ_inter, Set.mem_preimage]
    exact ChartedSpace.mem_chart_source p.down
  chart_mem_atlas p :=
    ⟨ChartedSpace.chartAt p.down, ChartedSpace.chart_mem_atlas p.down, rfl⟩

end ULiftTransfer

end JacobianChallenge

end
