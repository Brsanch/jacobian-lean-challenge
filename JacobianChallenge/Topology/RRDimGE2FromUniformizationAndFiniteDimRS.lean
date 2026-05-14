/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.RRDimGE2FromUniformizationAndFiniteDim
import JacobianChallenge.Topology.LinearSystemGermDeltaPFiniteDimTransport

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Final assembly: genus-0 RR dim ≥ 2 from uniformization + finite-dim on RS

Composing the existence and finite-dim transports yields the cleanest
form of the reduction: under the **single reference hypothesis**
`LinearSystemGermDeltaPFiniteDim RiemannSphere`, the genus-0 RR
dim ≥ 2 content on **any** compact connected complex 1-manifold `X`
reduces to **uniformization alone** at genus 0.

* The existence side (`ExistsSimplePoleGermAtSomePoint`) is
  unconditional on `RiemannSphere` (`Manifold/RiemannSphereSimplePole.lean`)
  and transports to `X` via a `HolomorphicEquiv X RS`
  (`Topology/ExistsSimplePoleGermFromHolomorphicEquivRS.lean`).
* The upper-bound side (`LinearSystemGermDeltaPFiniteDim`) transports
  in the same way (`Topology/LinearSystemGermDeltaPFiniteDimTransport.lean`).
  So `LinearSystemGermDeltaPFiniteDim X` reduces to
  `LinearSystemGermDeltaPFiniteDim RS` plus the equivalence.

## Contents

* `rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_RSFiniteDim` —
  `Nonempty (HolomorphicEquiv X RS) + LinearSystemGermDeltaPFiniteDim
  RS → RR_DimGE2_GenusZero_Germ X`.
* `rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim` —
  genus-conditional uniformization + `LinearSystemGermDeltaPFiniteDim
  RS → RR_DimGE2_GenusZero_Germ X`.

After this chip, the genus-0 RR dim ≥ 2 content on the germ field
sits on **exactly two classical inputs**:

1. **Uniformization at genus 0**:
   `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`.
2. **Finite-dim L(δp) on RS only**:
   `LinearSystemGermDeltaPFiniteDim RiemannSphere`.

Both are textbook classical content. Discharging the RS-side finite-dim
is a concrete Laurent-series computation (multi-chip but bounded);
uniformization at genus 0 is the deeper input.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace JacobianChallenge.MeromorphicFunctionField

universe u

open JacobianChallenge

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Final assembly -/

/-- **Genus-0 RR dim ≥ 2 from `HolomorphicEquiv X RS` and finite-dim on
RS only.** All other ingredients (existence side via the RS base case
and the transport) are unconditional. -/
theorem rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_RSFiniteDim
    (h_equiv : Nonempty (HolomorphicEquiv X RiemannSphere))
    (h_RS_finiteDim : LinearSystemGermDeltaPFiniteDim RiemannSphere) :
    RR_DimGE2_GenusZero_Germ X :=
  rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_finiteDim
    h_equiv
    (LinearSystemGermDeltaPFiniteDim.of_nonempty_holomorphicEquiv
      h_equiv h_RS_finiteDim)

/-- **Genus-0 RR dim ≥ 2 from genus-conditional uniformization and
finite-dim on RS only.** The cleanest reduction of the entire genus-0
RR dim ≥ 2 content to two named classical hypotheses (one a single
finite-dim claim on the RIEMANN SPHERE — a concrete computational
question — and the other the uniformization theorem at genus 0). -/
theorem rr_DimGE2_GenusZero_Germ_of_uniformization_and_RSFiniteDim
    (h_uniform : JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere))
    (h_RS_finiteDim : LinearSystemGermDeltaPFiniteDim RiemannSphere) :
    RR_DimGE2_GenusZero_Germ X := by
  intro hg
  exact rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_RSFiniteDim
    (h_uniform hg) h_RS_finiteDim hg

/-! ## Strict-containment companion (no FiniteDim needed) -/

/-- Strict-containment form needs no FiniteDim, since
`RR_StrictLt_of_existsSimplePoleGerm` is unconditional on FiniteDim. -/
theorem RR_StrictLt_GenusZero_Germ_of_uniformization' :
    (JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere)) →
    RR_StrictLt_GenusZero_Germ X :=
  RR_StrictLt_GenusZero_Germ_of_uniformization

/-! ## Full `RiemannRochGenusZero` (no FiniteDim needed via the
existence-side reduction) -/

/-- Full Riemann-Roch at genus zero from genus-conditional
uniformization. (Composes the simple-pole existence transport with the
existing `riemannRochGenusZero_from_ExistsSimplePoleGerm`.) -/
theorem riemannRochGenusZero_of_uniformization' :
    (JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere)) →
    JacobianChallenge.RiemannRochGenusZero X :=
  riemannRochGenusZero_of_uniformization

end JacobianChallenge.MeromorphicFunctionField

end
