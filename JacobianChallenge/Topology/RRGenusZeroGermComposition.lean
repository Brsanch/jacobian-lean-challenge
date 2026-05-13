/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.MeromorphicFunctionGermCanonicalize
import JacobianChallenge.Topology.HolomorphicLocallyConstantDischarge

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `RR_DimGE2_GenusZero_Germ` → `RiemannRochGenusZero` (unconditional)

The germ-side rebuild of the Riemann-Roch chain bottoms out here.
Combining the previous chips:

* `RRDimensionFormGerm` — `RR_DimGE2_GenusZero_Germ` + strict-lt + witness.
* `MeromorphicFunctionGermCanonicalize`'s
  `liftToMeromorphicNonzero` — non-constant germ in `L(δp)` ⇒
  `MeromorphicNonzero X` with order bounds + non-constancy.
* `HolomorphicLocallyConstantDischarge`'s
  `riemannRochGenusZero_from_existsBoundedByDeltaP` — the unconditional
  downstream theorem.

produces an **unconditional reduction** of `RiemannRochGenusZero X` to
just the single named classical input `RR_DimGE2_GenusZero_Germ X`,
replacing the broken 6-input chain stated against
`linearSystemDeltaP`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge.MeromorphicFunctionField

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`RR_DimGE2_GenusZero_Germ` ⇒ `ExistsNonConstantBoundedByDeltaP
_GenusZero`.** Combines the strict-containment witness extraction
from `RRDimensionFormGerm` with `liftToMeromorphicNonzero` from
`MeromorphicFunctionGermCanonicalize`. -/
theorem existsNonConstantBoundedByDeltaP_of_RR_DimGE2_Germ
    (hRR : RR_DimGE2_GenusZero_Germ X) :
    JacobianChallenge.ExistsNonConstantBoundedByDeltaP_GenusZero X := by
  intro hg
  -- Extract a non-constant germ in `L(δp)` for some `p`.
  obtain ⟨p, φ, hφ_in, hφ_not⟩ :=
    exists_mem_linearSystemGermDeltaP_not_constants_of_RR_DimGE2_Germ X hRR hg
  -- Lift to `MeromorphicNonzero X` with the bounds and non-constancy.
  obtain ⟨f, h_off, h_p, h_nc⟩ :=
    MeromorphicFunctionGerm.liftToMeromorphicNonzero hφ_in hφ_not
  refine ⟨p, f, h_off, h_p, h_nc⟩

/-- **Unconditional reduction of `RiemannRochGenusZero` to
`RR_DimGE2_GenusZero_Germ`.** The single remaining named classical
input is the dimension hypothesis on the germ field — a clean
Riemann-Roch + Serre-duality statement, not the broken pointwise one.

This is the germ-side replacement of
`JacobianChallenge.riemannRochGenusZero_from_RR_DimGE2_and_lifting`
from `Topology/RRGenusZeroFinrankChain.lean`, with the
`LiftToMeromorphicNonzero` hypothesis discharged. -/
theorem riemannRochGenusZero_from_RR_DimGE2_Germ
    (hRR : RR_DimGE2_GenusZero_Germ X) :
    JacobianChallenge.RiemannRochGenusZero X :=
  JacobianChallenge.riemannRochGenusZero_from_existsBoundedByDeltaP X
    (existsNonConstantBoundedByDeltaP_of_RR_DimGE2_Germ X hRR)

end JacobianChallenge.MeromorphicFunctionField

end
