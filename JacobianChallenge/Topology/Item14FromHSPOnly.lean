/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14ForwardFromCompactConnected
import JacobianChallenge.Topology.S2ImpliesGenus0FromEtalePrimitives

set_option linter.style.longLine false

/-! # Item 14 from `hSP X` alone

This file combines the forward-direction composition
`genus_eq_zero_iff_homeo_from_existsSimplePoleGerm`
(`Topology/Item14ForwardFromCompactConnected.lean:68`, takes
`hSP X + S2ImpliesGenus0 X`) with the **unconditional** reverse-leg
discharge `s2ImpliesGenus0_etalePrimitivesArc`
(`Topology/S2ImpliesGenus0FromEtalePrimitives.lean`, takes only the
standard manifold instance, sorry/axiom-free) to give a single-input
form of the Item 14 biconditional:

```
theorem genus_eq_zero_iff_homeo_from_hSP
    (hSP : ExistsSimplePoleGermAtSomePoint X) :
    genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)
```

This is the post-merge integration: BSLB / chart-cover admissibility /
path-primitive conditions are NOT in the input list — they were only
needed by the BSLB-route reverse leg, which is now obsolete (the
étale-primitives arc discharges the reverse leg unconditionally).

**Item 14's `sorry` in `Basic.lean:73` reduces, modulo this composition,
to a single named classical hypothesis: `ExistsSimplePoleGermAtSomePoint X`
on arbitrary X.**

Chip 2c-Final (`Manifold/ForsterCutoffPoleConstruction.lean`) reduces
hSP X further to `DBarSolvabilityAtGenusZero X + ChartAtConstantOnSource p`.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from `hSP X` alone.** The reverse direction
(`S2ImpliesGenus0 X`) is supplied internally by the unconditional
`s2ImpliesGenus0_etalePrimitivesArc`. The only open input is the
forward-leg simple-pole germ.

After the merge of `feat/item14-affineChartTriangleSimplex-ball`
(commit `829a6e8`, the étale-primitives arc Chips 1-4e), this is the
authoritative single-input form of Item 14. Older formulations
requiring BSLB, path-primitive admissibility, or chart-cover hypotheses
are now obsolete. -/
theorem genus_eq_zero_iff_homeo_from_hSP
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_existsSimplePoleGerm X hSP
    s2ImpliesGenus0_etalePrimitivesArc

end JacobianChallenge

end
