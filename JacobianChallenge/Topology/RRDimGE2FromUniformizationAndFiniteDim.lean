/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.ExistsSimplePoleGermFromHolomorphicEquivRS
import JacobianChallenge.Topology.LinearSystemDivisorSimplePoleRank
import JacobianChallenge.Topology.RRStrictLtFromSimplePole

set_option diagnostics true
set_option diagnostics.threshold 100
set_option linter.unusedSectionVars false

/-! # Assembly: genus-0 Riemann-Roch dim ≥ 2 from uniformization + finite-dim

This file composes the prior chips into clean headline theorems
reducing the genus-0 RR dim ≥ 2 content on the germ field to **two**
remaining named classical hypotheses:

1. **Uniformization** at genus 0:
   `genus X = 0 → Nonempty (HolomorphicEquiv X RiemannSphere)`.
2. **Finite-dimensionality of `L(δp)`** (the RR upper bound):
   `LinearSystemGermDeltaPFiniteDim X`.

Both are textbook classical RR / surface-theory content owed.

## Contents

* `rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_finiteDim` —
  from `Nonempty (HolomorphicEquiv X RS)` + `FiniteDim`, conclude
  `RR_DimGE2_GenusZero_Germ X`. (Genus hypothesis is **inside** the
  conclusion's `Prop`; this chip handles the case where uniformization
  is supplied unconditionally.)
* `rr_DimGE2_GenusZero_Germ_of_uniformization_and_finiteDim` — from
  the genus-conditional uniformization
  `genus X = 0 → Nonempty (HolomorphicEquiv X RS)` plus `FiniteDim`,
  conclude `RR_DimGE2_GenusZero_Germ X`.
* `RR_StrictLt_GenusZero_Germ_of_holomorphicEquiv_RS` — same chain
  for the strict-containment form (no finite-dim needed since
  `RR_StrictLt_of_existsSimplePoleGerm` is unconditional on
  finite-dim).
* `riemannRochGenusZero_of_holomorphicEquiv_RS` — full RR composition.

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

/-! ## Dim form -/

/-- **`RR_DimGE2_GenusZero_Germ X` from a `HolomorphicEquiv X
RiemannSphere` + finite-dimensionality.** -/
theorem rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_finiteDim
    (h_equiv : Nonempty (HolomorphicEquiv X RiemannSphere))
    (h_finiteDim : LinearSystemGermDeltaPFiniteDim X) :
    RR_DimGE2_GenusZero_Germ X :=
  rr_DimGE2_GenusZero_Germ_of_existsSimplePoleGerm_finiteDim
    (existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS h_equiv)
    h_finiteDim

/-- **`RR_DimGE2_GenusZero_Germ X` from genus-conditional uniformization
+ finite-dimensionality.** The classical genus-0 RR dim ≥ 2 fact on
the germ field, reduced to exactly the two textbook hypotheses. -/
theorem rr_DimGE2_GenusZero_Germ_of_uniformization_and_finiteDim
    (h_uniform : JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere))
    (h_finiteDim : LinearSystemGermDeltaPFiniteDim X) :
    RR_DimGE2_GenusZero_Germ X := by
  intro hg
  exact rr_DimGE2_GenusZero_Germ_of_holomorphicEquiv_RS_and_finiteDim
    (h_uniform hg) h_finiteDim hg

/-! ## Strict-containment form (no finite-dim needed) -/

/-- **`RR_StrictLt_GenusZero_Germ X` from a `HolomorphicEquiv X
RiemannSphere`.** The strict-containment form `constantsGerm <
linearSystemGermDeltaP p` is unconditional on finite-dimensionality
(only the linear-independence of `{1, ψ}` is needed). -/
theorem RR_StrictLt_GenusZero_Germ_of_holomorphicEquiv_RS
    (h_equiv : Nonempty (HolomorphicEquiv X RiemannSphere)) :
    RR_StrictLt_GenusZero_Germ X :=
  RR_StrictLt_of_existsSimplePoleGerm X
    (existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS h_equiv)

/-- **`RR_StrictLt_GenusZero_Germ X` from genus-conditional
uniformization.** -/
theorem RR_StrictLt_GenusZero_Germ_of_uniformization
    (h_uniform : JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere)) :
    RR_StrictLt_GenusZero_Germ X := by
  intro hg
  exact RR_StrictLt_GenusZero_Germ_of_holomorphicEquiv_RS (h_uniform hg) hg

/-! ## Full `RiemannRochGenusZero X` composition -/

/-- **Full `RiemannRochGenusZero X` from a `HolomorphicEquiv X
RiemannSphere`.** Composes the existence side (via the simple-pole
germ transport) with the existing
`riemannRochGenusZero_from_ExistsSimplePoleGerm`. -/
theorem riemannRochGenusZero_of_holomorphicEquiv_RS
    (h_equiv : Nonempty (HolomorphicEquiv X RiemannSphere)) :
    JacobianChallenge.RiemannRochGenusZero X :=
  riemannRochGenusZero_from_ExistsSimplePoleGerm X
    (existsSimplePoleGermAtSomePoint_of_holomorphicEquiv_RS h_equiv)

/-- **Full `RiemannRochGenusZero X` from genus-conditional
uniformization.** -/
theorem riemannRochGenusZero_of_uniformization
    (h_uniform : JacobianChallenge.genus X = 0 →
      Nonempty (HolomorphicEquiv X RiemannSphere)) :
    JacobianChallenge.RiemannRochGenusZero X := by
  intro hg
  exact riemannRochGenusZero_of_holomorphicEquiv_RS (h_uniform hg) hg

end JacobianChallenge.MeromorphicFunctionField

end
