/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.ComplexTorusDz
import JacobianChallenge.Manifold.ComplexTorusBasicInstances
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false

/-! # Genus lower bound on the complex torus: `1 ≤ genus (ℂ ⧸ L)`

End-to-end composition giving the lower bound

  `1 ≤ JacobianChallenge.genus (ℂ ⧸ L)`

unconditionally on the complex torus `T_L = ℂ ⧸ L`. The chain is:

1. **Forster Riesz** (`DiskChartCover.holomorphicOneFormFiniteDim_holds`)
   gives `Module.Finite ℂ (HolomorphicOneForm (ℂ ⧸ L))`, using the
   in-tree compactness + T2 + nonempty instances on `ℂ ⧸ L`
   (`ComplexTorusBasicInstances.lean`).

2. **`dz_ne_zero`** (`ComplexTorusDz.lean`) gives
   `Nontrivial (HolomorphicOneForm (ℂ ⧸ L))`.

3. `Module.finrank_pos_iff_of_free` on a finitely-generated free module
   over a field upgrades `Nontrivial` to `0 < Module.finrank`, hence
   `1 ≤ Module.finrank`.

This **closes half** of the `genus (ℂ ⧸ L) = 1` atom on `T_L`. The
complementary upper bound `Module.finrank ≤ 1` still requires the
Liouville-style argument on the universal cover.

## What this file ships

* `ComplexTorus.holomorphicOneFormFiniteDim_torus` — Forster Riesz
  applied on `ℂ ⧸ L`.
* `ComplexTorus.one_le_finrank_holomorphicOneForm` — the lower bound
  on the `ℂ`-dimension of `HolomorphicOneForm (ℂ ⧸ L)`.
* `ComplexTorus.one_le_genus` — the genus lower bound.

No `sorry`, no `axiom`. -/

open Module
open scoped Manifold ContDiff

noncomputable section

namespace JacobianChallenge

namespace ComplexTorus

variable (L : Submodule ℤ ℂ)
  [DiscreteTopology L] [IsZLattice ℝ L]

/-! ## Forster Riesz applied on `ℂ ⧸ L` -/

/-- **`HolomorphicOneFormFiniteDim (ℂ ⧸ L)` holds unconditionally.**
Direct application of `DiskChartCover.holomorphicOneFormFiniteDim_holds`
on the torus, using the basic instances from
`ComplexTorusBasicInstances.lean`. -/
theorem holomorphicOneFormFiniteDim_torus :
    HolomorphicOneFormFiniteDim (ℂ ⧸ L) :=
  DiskChartCover.holomorphicOneFormFiniteDim_holds

/-- `Module.Finite ℂ (HolomorphicOneForm (ℂ ⧸ L))` as a typeclass-level
instance, via Forster Riesz. -/
instance instModuleFinite :
    Module.Finite ℂ (HolomorphicOneForm (ℂ ⧸ L)) :=
  (holomorphicOneFormFiniteDim_torus L).toModuleFinite

/-- `FiniteDimensional ℂ (HolomorphicOneForm (ℂ ⧸ L))` as a
typeclass-level instance, via Forster Riesz. -/
instance instFiniteDimensional :
    FiniteDimensional ℂ (HolomorphicOneForm (ℂ ⧸ L)) :=
  finiteDimensional_of_HolomorphicOneFormFiniteDim
    (holomorphicOneFormFiniteDim_torus L)

/-! ## Genus lower bound: `1 ≤ Module.finrank` -/

/-- **`1 ≤ Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L))`.** Composes
the Forster Riesz finite-dim discharge with `dz_ne_zero` (via
`nontrivial_holomorphicOneForm`) and `Module.finrank_pos_iff_of_free`
(applicable because we are over the field ℂ, with Free + Finite). -/
theorem one_le_finrank_holomorphicOneForm :
    1 ≤ Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L)) := by
  -- Nontrivial from dz_ne_zero.
  haveI : Nontrivial (HolomorphicOneForm (ℂ ⧸ L)) :=
    nontrivial_holomorphicOneForm L
  -- 0 < finrank ↔ Nontrivial on Free + Finite module over a field.
  -- Module.Finite is by the instance above. Module.Free is automatic for
  -- finite modules over a field.
  have h_pos : 0 < Module.finrank ℂ (HolomorphicOneForm (ℂ ⧸ L)) :=
    (Module.finrank_pos_iff (R := ℂ)).mpr inferInstance
  exact h_pos

/-- **`1 ≤ JacobianChallenge.genus (ℂ ⧸ L)`.** Restatement using
`genus X := Module.finrank ℂ (HolomorphicOneForm X)`. -/
theorem one_le_genus :
    1 ≤ JacobianChallenge.genus (ℂ ⧸ L) :=
  one_le_finrank_holomorphicOneForm L

end ComplexTorus

end JacobianChallenge

end
