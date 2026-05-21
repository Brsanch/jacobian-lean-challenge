/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Analysis.Complex.Basic

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

/-- **Transition-map identity:** the chart transition between two
ULift-composed charts agrees on source with the corresponding
transition map downstairs.

This is the key lemma feeding `uliftHasGroupoid`. -/
lemma ulift_charts_eqOnSource {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (h : ULift.{u} Y ≃ₜ Y)
    (a b : OpenPartialHomeomorph Y Z) :
    (h.toOpenPartialHomeomorph.trans a).symm.trans
        (h.toOpenPartialHomeomorph.trans b) ≈ a.symm.trans b := by
  calc (h.toOpenPartialHomeomorph.trans a).symm.trans
          (h.toOpenPartialHomeomorph.trans b)
      = (a.symm.trans h.toOpenPartialHomeomorph.symm).trans
          (h.toOpenPartialHomeomorph.trans b) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    _ = a.symm.trans
          ((h.toOpenPartialHomeomorph.symm.trans
            h.toOpenPartialHomeomorph).trans b) := by
        rw [OpenPartialHomeomorph.trans_assoc,
          OpenPartialHomeomorph.trans_assoc]
    _ ≈ a.symm.trans ((OpenPartialHomeomorph.ofSet
            h.toOpenPartialHomeomorph.target (by
              simp [Homeomorph.toOpenPartialHomeomorph])).trans b) := by
        exact OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _)
          (OpenPartialHomeomorph.EqOnSource.trans'
            (OpenPartialHomeomorph.symm_trans_self _) (Setoid.refl _))
    _ = a.symm.trans ((OpenPartialHomeomorph.ofSet
            Set.univ isOpen_univ).trans b) := by
        simp [Homeomorph.toOpenPartialHomeomorph]
    _ ≈ a.symm.trans b := by
        refine OpenPartialHomeomorph.EqOnSource.trans' (Setoid.refl _) ?_
        rw [OpenPartialHomeomorph.ofSet_univ_eq_refl,
          OpenPartialHomeomorph.refl_trans]

/-- **`HasGroupoid` transfers from `M` to `ULift M`** under the
charted-space structure `chartedSpaceULift`. -/
@[reducible] noncomputable def uliftHasGroupoid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {I : ModelWithCorners ℂ E H} {n : WithTop ℕ∞}
    [HasGroupoid M (contDiffGroupoid n I)] :
    letI : ChartedSpace H (ULift M) := chartedSpaceULift
    HasGroupoid (ULift M) (contDiffGroupoid n I) := by
  letI : ChartedSpace H (ULift M) := chartedSpaceULift
  refine ⟨?_⟩
  rintro e e' ⟨a, haMem, rfl⟩ ⟨b, hbMem, rfl⟩
  exact StructureGroupoid.mem_of_eqOnSource _
    (HasGroupoid.compatible haMem hbMem)
    (ulift_charts_eqOnSource Homeomorph.ulift a b)

end ULiftTransfer

end JacobianChallenge

end
