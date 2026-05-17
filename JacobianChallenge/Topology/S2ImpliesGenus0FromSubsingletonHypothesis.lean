/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromSimplyConnected
import JacobianChallenge.Topology.SimplyConnectedS2Unconditional
import JacobianChallenge.Topology.Item14ForwardFromCompactConnected

set_option linter.style.longLine false

/-! # `S2ImpliesGenus0` from the single classical input
`HolomorphicOneFormSubsingletonOfSimplyConnected`

The chip `s2ImpliesGenus0_from_simplyConnected` in
`S2ImpliesGenus0FromSimplyConnected.lean` reduces `S2ImpliesGenus0 X` to
two classical inputs:

* `SimplyConnectedS2` (π₁(S²) trivial)
* `HolomorphicOneFormSubsingletonOfSimplyConnected X`

Of these, `SimplyConnectedS2` is now **unconditional** at the mathlib
pin via `simplyConnectedS2_holds` (the 15-chip Phase-3 smoothing arc,
landed 2026-05-15 in `Topology/SimplyConnectedS2Unconditional.lean`).

This file specialises the reduction to use the unconditional
`simplyConnectedS2_holds` internally, so the only remaining input is
the analytic one (`HolomorphicOneFormSubsingletonOfSimplyConnected`).

We also assemble the resulting bundled biconditional for item 14 from
the same single analytic input on the reverse leg, combined with
`ExistsSimplePoleGermAtSomePoint X` on the forward leg (already
post-Item14ForwardFromCompactConnected, no `[FiniteDimensional]` needed
externally).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`S2ImpliesGenus0 X` from the single analytic input
`HolomorphicOneFormSubsingletonOfSimplyConnected X`.** The
`SimplyConnectedS2` premise is discharged internally via the
unconditional `simplyConnectedS2_holds`. -/
theorem s2ImpliesGenus0_from_subsingletonOfSimplyConnected
    (h_sub : HolomorphicOneFormSubsingletonOfSimplyConnected X) :
    S2ImpliesGenus0 X :=
  s2ImpliesGenus0_from_simplyConnected X simplyConnectedS2_holds h_sub

/-- **Full Item 14 bundle from two classical inputs.** The forward leg
needs `ExistsSimplePoleGermAtSomePoint X` (genus-0 RR existence). The
reverse leg needs `HolomorphicOneFormSubsingletonOfSimplyConnected X`
(simply-connected ⇒ subsingleton holomorphic 1-forms; the analytic
content of Stokes + Liouville). -/
theorem surfaceClassificationGenus_from_subsingletonOfSimplyConnected
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_sub : HolomorphicOneFormSubsingletonOfSimplyConnected X) :
    SurfaceClassificationGenus X :=
  surfaceClassificationGenus_from_existsSimplePoleGerm X hSP
    (s2ImpliesGenus0_from_subsingletonOfSimplyConnected X h_sub)

/-- **Item 14 biconditional from the two classical inputs.** -/
theorem genus_eq_zero_iff_homeo_from_subsingletonOfSimplyConnected
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_sub : HolomorphicOneFormSubsingletonOfSimplyConnected X) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  (surfaceClassificationGenus_from_subsingletonOfSimplyConnected X hSP h_sub).toIff

end JacobianChallenge

end
