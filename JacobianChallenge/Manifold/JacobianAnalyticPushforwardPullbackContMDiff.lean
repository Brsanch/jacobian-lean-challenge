/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.PeriodLatticeLinearQuotient
import JacobianChallenge.Manifold.JacobianOfLatticeFromBundle

/-! # ContMDiff of analytic-Jacobian-level pushforward/pullback (items 18, 21)

OPEN.md items 18 (`pushforward_contMDiff`) and 21 (`pullback_contMDiff`)
state smoothness of `Jacobian X →ₜ+ Jacobian Y` maps for `f : X → Y`
(non-constant smooth). On the analytic Jacobian, both are induced by
ℂ-linear lifts on the universal cover:

  pushforward_T_f : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus Y) → ℂ)
  pullback_T_f : (Fin (genus Y) → ℂ) →L[ℂ] (Fin (genus X) → ℂ)

each carrying the source lattice into the target lattice. The
descended map on the period quotient is `ContMDiff` by
`quotientLinearMap_contMDiff` (sister file
`PeriodLatticeLinearQuotient.lean`).

This file packages that observation in the analytic-Jacobian's actual
shape: given a bundle `data_X, α_X, h_X` for `X` and `data_Y, α_Y, h_Y`
for `Y`, and a ℂ-linear lift `T` carrying the period image of `data_X`
into the period image of `data_Y`, the induced map on
`AnalyticJacobian` is `ContMDiff`.

The lift `T_f` (and the lattice-matching condition) for a specific
holomorphic curve map `f` is supplied by integrating `f^* α_Y` (resp.
`f_* α_X`); construction of `T_f` is genuinely separate analytic work
(part of the C3 work in `CLOSURE_MAP.md`). What this file delivers is
**the smoothness conclusion** once the lift is provided — the missing
piece for OPEN.md items 18 and 21 once C3 is closed.

## Net contribution

* `analyticJacobian_linearLift_contMDiff` — `ContMDiff` of the
  AnalyticJacobian-level map induced by a ℂ-linear cover lift. The
  Basic.lean-level statement (after C3 rewires `Jacobian X` to
  `AnalyticJacobian X _ _`) follows by `AddEquiv` transport.
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

/-- **Item 18/21 building block.** `ContMDiff` of the
AnalyticJacobian-level map induced by a ℂ-linear cover lift `T` that
carries `data_X.lattice` into `data_Y.lattice`. Reduces directly to
`quotientLinearMap_contMDiff`. -/
theorem analyticJacobian_linearLift_contMDiff
    (data_X : PeriodLatticeOfRankTwoG X)
    (data_Y : PeriodLatticeOfRankTwoG Y)
    [DiscreteTopology data_X.lattice.toIntSubmodule]
    [IsZLattice ℝ data_X.lattice.toIntSubmodule]
    [DiscreteTopology data_Y.lattice.toIntSubmodule]
    [IsZLattice ℝ data_Y.lattice.toIntSubmodule]
    (T : (Fin (JacobianChallenge.genus X) → ℂ) →L[ℂ]
          (Fin (JacobianChallenge.genus Y) → ℂ))
    (hT : ∀ x ∈ data_X.lattice.toIntSubmodule, T x ∈ data_Y.lattice.toIntSubmodule) :
    ContMDiff (𝓘(ℂ, Fin (JacobianChallenge.genus X) → ℂ))
              (𝓘(ℂ, Fin (JacobianChallenge.genus Y) → ℂ)) ω
      (quotientLinearMap data_X.lattice.toIntSubmodule
        data_Y.lattice.toIntSubmodule T hT) :=
  quotientLinearMap_contMDiff
    data_X.lattice.toIntSubmodule data_Y.lattice.toIntSubmodule ω T hT

end JacobianChallenge

end
