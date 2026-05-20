/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14From4MinimalInputs

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional under `Subsingleton (HolomorphicOneForm X)`

When `HolomorphicOneForm X` is subsingleton (forces `genus X = 0` by
the `Module.finrank` body of `genus`), the per-basis hypotheses
`h_smooth_b` and `h_ftc_b` become **vacuous**: any basis on a
subsingleton module has empty index type (since the underlying
ℂ-module has dimension 0). The minimal-input count of item 14 thus
drops from 4 to **2** in this regime:

* `hSP` — `ExistsSimplePoleGermAtSomePoint X` (forward leg).
* `h_bslb` — `SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis ...`
  (reverse leg, smooth-Hurewicz at genus 0).

The `Subsingleton (HolomorphicOneForm X)` hypothesis is unconditional
on `RS` (via `Manifold/RiemannSphereChartSCoeffOverlap.lean`) and on
the universal cover `ℂ` (via subsingleton holomorphic one-forms on ℂ
modulo periodicity). It's also implied by `genus X = 0 + finite-
dimensional H⁰(X, Ω¹)` (the latter is in tree unconditionally via
`DiskChartCover.holomorphicOneFormFiniteDim_holds`).

## What this file ships

* `genus_eq_zero_iff_homeo_from_2_minimal_inputs_under_subsingleton`
  — item 14 biconditional with vacuous per-basis hypotheses.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional under `Subsingleton (HolomorphicOneForm X)`,
from 2 minimal named hypotheses.**

Under the subsingleton hypothesis, any basis of `HolomorphicOneForm X`
has empty index type, making the per-basis smoothness/FTC checks
vacuous. The remaining named hypotheses are:

* `hSP : ExistsSimplePoleGermAtSomePoint X` (forward leg).
* `h_bslb : SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`
  (reverse leg).

Equivalent to `genus_eq_zero_iff_homeo_from_4_minimal_inputs` instantiated
at the empty basis on a subsingleton ω-module. -/
theorem genus_eq_zero_iff_homeo_from_2_minimal_inputs_under_subsingleton
    (x₀ : X) [Subsingleton (HolomorphicOneForm X)]
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  -- Since HolomorphicOneForm X is subsingleton, finrank = 0, so
  -- Module.finBasis ℂ (HolomorphicOneForm X) is indexed by Fin 0 = empty.
  -- We use FiniteDimensional content unconditionally from
  -- DiskChartCover.holomorphicOneFormFiniteDim_holds (already in tree).
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X)
  have hrank_zero : Module.finrank ℂ (HolomorphicOneForm X) = 0 :=
    Module.finrank_zero_of_subsingleton
  haveI hempty : IsEmpty (Fin (Module.finrank ℂ (HolomorphicOneForm X))) := by
    rw [hrank_zero]; infer_instance
  exact genus_eq_zero_iff_homeo_from_4_minimal_inputs (X := X) x₀
    (Module.finBasis ℂ (HolomorphicOneForm X)) hSP h_bslb
    (fun _ i => isEmptyElim i)
    (fun _ i _ => isEmptyElim i)

end JacobianChallenge

end
