/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.BilinearFromHodgeChain
import JacobianChallenge.Manifold.HodgeInnerProductUnconditional

set_option linter.unusedSectionVars false

/-! # `CompleteHodgeRiemannHypothesis` via `standardHodgeForm` (chip 11)

Chip 10 discharged `HodgeInnerProductHypothesis X` unconditionally via
the `standardHodgeForm basis_ω` construction. This file leverages that
to provide a simplified form of `CompleteHodgeRiemannHypothesis` that
**no longer requires the user to supply `H` and prove positivity**.

The simplified form:

  `CompleteHodgeRiemannHypothesisViaStandardForm ... := ∃ J, first ∧ bridge(J, standardHodgeForm basis_ω)`

implies the full `CompleteHodgeRiemannHypothesis ...` via existential
introduction with `H := standardHodgeForm basis_ω` + the
`standardHodgeForm_isPositiveDefinite` chip 10 atom.

Net effect: the user now needs to supply just `(J, first relation,
bridge identity)` rather than `(J, H, PD, first, bridge)`.

## What this file ships

* `CompleteHodgeRiemannHypothesisViaStandardForm` — the simplified Prop.
* `completeHodgeRiemannHypothesis_of_viaStandardForm` — bridge to the
  full form.
* `nonempty_smoothHomologyDataPackage_of_hodgeChain_via_standardForm` —
  convenience wrapper composing this with chip 4.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Matrix Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Simplified Hodge-Riemann bundle** using the unconditional
`standardHodgeForm`. The user supplies only `J` and the matrix
relations; the Hodge form and its positivity are automatic. -/
def CompleteHodgeRiemannHypothesisViaStandardForm
    (data : PeriodPairingData X)
    (basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X))
    (cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1) : Prop :=
  ∃ (J : Matrix (Fin (2 * JacobianChallenge.genus X))
          (Fin (2 * JacobianChallenge.genus X)) ℤ),
    RiemannBilinearFirstRelation data basis_ω cycleGens J ∧
    HodgeRiemannBridgeHypothesis data basis_ω cycleGens J
      (standardHodgeForm basis_ω)

/-- **Bridge: simplified form ⟹ full form.** -/
theorem completeHodgeRiemannHypothesis_of_viaStandardForm
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h : CompleteHodgeRiemannHypothesisViaStandardForm data basis_ω cycleGens) :
    CompleteHodgeRiemannHypothesis data basis_ω cycleGens := by
  obtain ⟨J, hFirst, hBridge⟩ := h
  refine ⟨J, standardHodgeForm basis_ω, ?_, hFirst, hBridge⟩
  exact standardHodgeForm_isPositiveDefinite basis_ω

/-- **Convenience corollary**: ℝ-LI of period vectors from the
simplified form. -/
theorem realLI_periodVector_of_viaStandardForm
    {data : PeriodPairingData X}
    {basis_ω : Basis (Fin (JacobianChallenge.genus X)) ℂ
      (HolomorphicOneForm X)}
    {cycleGens : Fin (2 * JacobianChallenge.genus X) → data.H1}
    (h : CompleteHodgeRiemannHypothesisViaStandardForm data basis_ω cycleGens) :
    LinearIndependent ℝ
      (fun i : Fin (2 * JacobianChallenge.genus X) =>
        periodVector data basis_ω (cycleGens i)) :=
  realLI_periodVector_of_completeHodgeRiemann
    (completeHodgeRiemannHypothesis_of_viaStandardForm h)

end JacobianChallenge

end
