/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14From4MinimalInputs
import JacobianChallenge.Topology.Item14FromTwoNamedClassical
import JacobianChallenge.Manifold.HasAdmissibleChartCoverFromConvexChartAtTarget
import JacobianChallenge.Manifold.LoopPeriodVanishesOfBasedSmoothLoopsBound
import Mathlib.LinearAlgebra.Basis.Defs

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 from 2 classical inputs under `[HasConvexChartAtTarget X]`

Composes [`genus_eq_zero_iff_homeo_from_4_minimal_inputs`](Item14From4MinimalInputs.lean)
with the structural typeclass

  `HasConvexChartAtTarget X : ∀ x, Convex ℝ (chartAt ℂ x).target`

(from [`HasAdmissibleChartCoverFromConvexChartAtTarget.lean`](../Manifold/HasAdmissibleChartCoverFromConvexChartAtTarget.lean))
to auto-discharge **both** primitive-side hypotheses (`h_smooth_b` and
`h_ftc_b`) of the 4-input formulation, leaving only the two genuinely
classical hypotheses as explicit inputs:

* `hSP : ExistsSimplePoleGermAtSomePoint X` (forward leg, RR-class);
* `h_bslb : SimplyConnected → BasedSmoothLoopsBoundHypothesis ...`
  (reverse leg, smooth-Hurewicz at genus 0).

The auto-discharge chain:

* `[HasConvexChartAtTarget X]` ⟹ `[HasAdmissibleChartCover X]`
  (via chips C + D5 wired up in
  `instHasAdmissibleChartCoverOfConvexChartAtTarget`);
* `h_bslb (sc)` ⟹ `LoopPeriodVanishes om x₀` for every `om`
  (via `loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis`);
* `[HasAdmissibleChartCover X]` + `LoopPeriodVanishes` ⟹ global
  `ContMDiff ω` of `pathPrimitive`
  (via `pathPrimitive_contMDiff_of_HasAdmissibleChartCover`);
* `[HasAdmissibleChartCover X]` + `LoopPeriodVanishes` ⟹ global FTC
  (via `pathPrimitive_eval_eq_mfderiv_of_HasAdmissibleChartCover`).

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Set Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from 2 classical inputs under
`[HasConvexChartAtTarget X]`.**

After this composition, the only remaining named hypotheses for
item 14 on `X` with `[HasConvexChartAtTarget X]` are the two genuine
classical statements:

* `hSP` — `ExistsSimplePoleGermAtSomePoint X` (forward leg).
* `h_bslb` — `SimplyConnected → BasedSmoothLoopsBoundHypothesis ...`
  (reverse leg).

Both `h_smooth_b` (primitive ContMDiff) and `h_ftc_b` (primitive FTC)
of the 4-input version are auto-discharged via the new
`HasAdmissibleChartCover X` instance from chips C + D5. -/
theorem genus_eq_zero_iff_homeo_from_2_classical_inputs_under_convexChartAt
    [HasConvexChartAtTarget X]
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  -- Auto-discharge `h_smooth_b` via the class-driven path-primitive ContMDiff.
  have h_smooth_b : ∀ (_ : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (smoothPathConnected_of_preconnected) x₀ (b i)) := by
    intro sc i
    have h_loop : LoopPeriodVanishes (b i) x₀ :=
      loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis (h_bslb sc) (b i)
    exact pathPrimitive_contMDiff_of_HasAdmissibleChartCover
      (smoothPathConnected_of_preconnected) x₀ (b i) h_loop
  -- Auto-discharge `h_ftc_b` via the class-driven path-primitive FTC.
  have h_ftc_b : ∀ (_ : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (smoothPathConnected_of_preconnected) x₀ (b i)) x := by
    intro sc i x
    have h_loop : LoopPeriodVanishes (b i) x₀ :=
      loopPeriodVanishes_of_basedSmoothLoopsBoundHypothesis (h_bslb sc) (b i)
    exact pathPrimitive_eval_eq_mfderiv_of_HasAdmissibleChartCover
      (smoothPathConnected_of_preconnected) x₀ (b i) h_loop x
  exact genus_eq_zero_iff_homeo_from_4_minimal_inputs x₀ b hSP h_bslb
    h_smooth_b h_ftc_b

end JacobianChallenge

end
