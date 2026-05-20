/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14FromTwoNamedClassical
import JacobianChallenge.Manifold.SmoothPathLocalConvex

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional from 4 minimal named hypotheses

Strengthens `genus_eq_zero_iff_homeo_from_minimal_inputs` (which
required 5 named inputs) by discharging the smooth-path-connectedness
atom unconditionally via `smoothPathConnected_of_preconnected`. The
`[ConnectedSpace X]` typeclass hypothesis is already in scope (part
of the standard challenge typeclass context).

Reduces the named-hypothesis count of item 14 from 5 to **4 minimal
named classical hypotheses**:

* `ExistsSimplePoleGermAtSomePoint X` (forward leg, RR-class).
* `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` (reverse leg,
  smooth-Hurewicz at genus 0).
* Per-basis `ContMDiff ω (pathPrimitive ...)` (reverse leg,
  primitive smoothness).
* Per-basis FTC at `eval` (reverse leg, primitive recovers eval).

The `pathPrimitive ...` and `eval`-FTC inputs are still parametric on
`SimplyConnectedSpace X`, since the choice of base point + smooth-path-
connectedness used in `pathPrimitive` enters per-instance. But the
*construction* of the SmoothPathConnected witness is now automatic
from `[ConnectedSpace X]` (no longer a separate named hypothesis).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from 4 minimal named hypotheses.**

Compared to `genus_eq_zero_iff_homeo_from_minimal_inputs`, the
`h_conn_from_sc : SimplyConnectedSpace X → SmoothPathConnected 𝓘(ℝ, ℂ) X`
named hypothesis is discharged unconditionally via
`smoothPathConnected_of_preconnected` (already in tree at
`Manifold/SmoothPathLocalConvex.lean`): on any preconnected complex
1-manifold, smooth-path-connectedness is automatic.

The four remaining named hypotheses are:

* `hSP` — `ExistsSimplePoleGermAtSomePoint X` (forward leg, RR-class).
* `h_bslb` — `SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis
  𝓘(ℝ, ℂ) X x₀` (reverse leg, smooth-Hurewicz at genus 0).
* `h_smooth_b` — per-basis `ContMDiff ω (pathPrimitive ...)` (reverse
  leg, primitive smoothness against the auto-discharged
  `SmoothPathConnected` witness).
* `h_ftc_b` — per-basis FTC at `eval` (reverse leg, primitive recovers
  eval against the auto-discharged witness). -/
theorem genus_eq_zero_iff_homeo_from_4_minimal_inputs
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth_b : ∀ (_ : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (smoothPathConnected_of_preconnected) x₀ (b i)))
    (h_ftc_b : ∀ (_ : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (smoothPathConnected_of_preconnected) x₀ (b i)) x) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_minimal_inputs x₀ b hSP
    (fun _ => smoothPathConnected_of_preconnected)
    h_bslb h_smooth_b h_ftc_b

end JacobianChallenge

end
