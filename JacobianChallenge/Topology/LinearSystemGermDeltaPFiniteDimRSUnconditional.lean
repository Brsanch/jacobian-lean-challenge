/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemGermDeltaPFiniteDimRSFromInputs
import JacobianChallenge.Topology.LinearSystemAtInftyRSDischarge
import JacobianChallenge.Topology.RRDimGE2FromUniformizationAndFiniteDimRS
import JacobianChallenge.Manifold.MobiusTransitivityRS

set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # `LinearSystemGermDeltaPFiniteDim RiemannSphere` — unconditional

The genus-0 Riemann–Roch chain on the Riemann sphere reduces (per
`Topology/LinearSystemGermDeltaPFiniteDimRSFromInputs.lean`) to two
named classical inputs:

1. `LinearSystemAtInftyRS_BoundedBySimplePoleSpan` — polynomial-growth
   Liouville at `∞`. **Discharged** 2026-05-14
   (`Topology/LinearSystemAtInftyRSDischarge.lean`,
   `linearSystemAtInftyRS_boundedBySimplePoleSpan`).
2. `ExistsMobiusToInftyRS` — Möbius transitivity on RS. **Discharged**
   2026-05-14 via `feat/antipode-smoothness`
   (`Manifold/MobiusTransitivityRS.lean`,
   `RiemannSphere.existsMobiusToInftyRS`).

This file composes the two discharges to obtain
`LinearSystemGermDeltaPFiniteDim RiemannSphere` **unconditionally**:
no remaining hypothesis. The genus-0 RR `dim_ℂ L(δp) ≥ 2` chain now
reduces, for an arbitrary genus-0 compact connected complex
1-manifold `X`, to **one** remaining classical input — uniformization
at genus 0 (`genus X = 0 → Nonempty (HolomorphicEquiv X
RiemannSphere)`).

## What ships

* `existsMobiusToInftyRS_holds : ExistsMobiusToInftyRS` — bridge
  identifying the in-tree theorem `RiemannSphere.existsMobiusToInftyRS`
  with the named-hypothesis Prop. Definitional equality; `rfl`.
* `linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
  LinearSystemGermDeltaPFiniteDim RiemannSphere` — the headline
  consequence of A1 + A2.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge.MeromorphicFunctionField

universe u

open JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **A2 discharge bridge.** The named-hypothesis Prop
`ExistsMobiusToInftyRS` (defined in
`Topology/LinearSystemGermDeltaPFiniteDimRSFromInputs.lean`) is
definitionally the statement of
`RiemannSphere.existsMobiusToInftyRS`
(`Manifold/MobiusTransitivityRS.lean`). The bridge is `rfl`. -/
theorem existsMobiusToInftyRS_holds : ExistsMobiusToInftyRS :=
  JacobianChallenge.RiemannSphere.existsMobiusToInftyRS

/-- **`LinearSystemGermDeltaPFiniteDim RiemannSphere` unconditionally.**

Composes:
* `linearSystemAtInftyRS_boundedBySimplePoleSpan` (A1, discharged
  via polynomial-growth Liouville at `∞`), and
* `existsMobiusToInftyRS_holds` (A2, discharged via the
  Möbius transitivity assembly: identity at `∞` and
  `translateEquiv (-z₀) ∘ antipodeEquiv` at finite `coe z₀`).

The combined result is `Module.Finite ℂ (linearSystemGermDeltaP p)`
for every `p : RiemannSphere`, with no remaining hypothesis. -/
theorem linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional :
    LinearSystemGermDeltaPFiniteDim RiemannSphere :=
  linearSystemGermDeltaPFiniteDim_RiemannSphere
    linearSystemAtInftyRS_boundedBySimplePoleSpan
    existsMobiusToInftyRS_holds

/-- **Genus-0 RR `dim ≥ 2` on the germ field — `X` reduced to
uniformization alone.** Composes the unconditional
`LinearSystemGermDeltaPFiniteDim RiemannSphere` (A1 + A2 discharged)
with the existing assembly `rr_DimGE2_GenusZero_Germ_of_uniformization
_and_RSFiniteDim`. For any compact connected complex 1-manifold `X`,
the genus-0 RR dim ≥ 2 content now depends on **a single** remaining
classical input: genus-conditional uniformization at genus 0
(`genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`). -/
theorem rr_DimGE2_GenusZero_Germ_of_uniformization_unconditional_RSFiniteDim
    (h_uniform : JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere)) :
    RR_DimGE2_GenusZero_Germ X :=
  rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim
    h_uniform
    linearSystemGermDeltaPFiniteDim_RiemannSphere_unconditional

end JacobianChallenge.MeromorphicFunctionField

end
