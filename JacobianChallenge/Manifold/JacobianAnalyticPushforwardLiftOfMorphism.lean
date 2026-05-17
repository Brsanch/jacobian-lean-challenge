/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.JacobianAnalyticPushforwardLiftOfCurve
import JacobianChallenge.Manifold.PeriodPairingMorphism

set_option linter.unusedSectionVars false

/-! # Final integration: `JacobianAnalyticPushforwardLift.ofMorphism`

Combines the per-curve constructor (`JacobianAnalyticPushforwardLift.ofCurveMap`)
with the period-adjunction certificate (`PeriodPairingMorphism.lattice_match`)
to produce a `JacobianAnalyticPushforwardLift` from a **single** named
hypothesis: a `PeriodPairingMorphism` between the underlying period
pairings.

This is the cleanest single-input form for downstream callers: supply a
curve map + cycle pushforward + adjunction certificate (the
`PeriodPairingMorphism` bundle), and obtain the analytic-Jacobian-level
pushforward lift with full `ContMDiff` discharge (via the existing
`toQuotientMap_contMDiff`).

## Headline

```
JacobianAnalyticPushforwardLift.ofMorphism
    (αX, αY)
    (data_X = PeriodLatticeOfRankTwoG.ofPeriodPairing pairing_X αX hyp_X)
    (data_Y = PeriodLatticeOfRankTwoG.ofPeriodPairing pairing_Y αY hyp_Y)
    (morph : PeriodPairingMorphism pairing_X pairing_Y)
    : JacobianAnalyticPushforwardLift data_X data_Y
```

The construction:
* `f := morph.f`, `contMDiff_f := morph.contMDiff_f`.
* `T := HolomorphicOneForm.pushforwardLinearLift αX αY morph.f morph.contMDiff_f`.
* `lattice_match := morph.lattice_match αX αY` (via the
  `ofPeriodPairing_lattice` rewrite identifying `data.lattice` with
  `periodLatticeImage`).
-/

open scoped ContDiff Manifold
open Submodule Module

noncomputable section

namespace JacobianChallenge

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **`JacobianAnalyticPushforwardLift` from a `PeriodPairingMorphism`.**
Single-input form: given the period-adjunction bundle, produce the
analytic-Jacobian-level pushforward lift. -/
noncomputable def JacobianAnalyticPushforwardLift.ofMorphism
    (pairing_X : PeriodPairingData X)
    (pairing_Y : PeriodPairingData Y)
    (αX : Basis (Fin (JacobianChallenge.genus X)) ℂ (HolomorphicOneForm X))
    (αY : Basis (Fin (JacobianChallenge.genus Y)) ℂ (HolomorphicOneForm Y))
    (hyp_X : PeriodLatticeAnalyticHypotheses pairing_X αX)
    (hyp_Y : PeriodLatticeAnalyticHypotheses pairing_Y αY)
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofPeriodPairing
        pairing_X αX hyp_X).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofPeriodPairing
        pairing_X αX hyp_X).lattice.toIntSubmodule]
    [DiscreteTopology
      (PeriodLatticeOfRankTwoG.ofPeriodPairing
        pairing_Y αY hyp_Y).lattice.toIntSubmodule]
    [IsZLattice ℝ
      (PeriodLatticeOfRankTwoG.ofPeriodPairing
        pairing_Y αY hyp_Y).lattice.toIntSubmodule]
    (morph : PeriodPairingMorphism pairing_X pairing_Y) :
    JacobianAnalyticPushforwardLift
      (PeriodLatticeOfRankTwoG.ofPeriodPairing pairing_X αX hyp_X)
      (PeriodLatticeOfRankTwoG.ofPeriodPairing pairing_Y αY hyp_Y) :=
  JacobianAnalyticPushforwardLift.ofCurveMap
    (PeriodLatticeOfRankTwoG.ofPeriodPairing pairing_X αX hyp_X)
    (PeriodLatticeOfRankTwoG.ofPeriodPairing pairing_Y αY hyp_Y)
    αX αY morph.f morph.contMDiff_f
    (by
      intro v hv
      -- `data.lattice = periodLatticeImage` definitionally; `toIntSubmodule`
      -- preserves the underlying set (`AddSubgroup.coe_toIntSubmodule`).
      -- Membership in a `Submodule ℤ` is membership in the underlying set.
      have hv_set : v ∈ (periodLatticeImage pairing_X αX : Set _) := hv
      have h_match : HolomorphicOneForm.pushforwardLinearLift αX αY morph.f
            morph.contMDiff_f v
          ∈ periodLatticeImage pairing_Y αY :=
        morph.lattice_match αX αY v hv_set
      exact h_match)

end JacobianChallenge

end
