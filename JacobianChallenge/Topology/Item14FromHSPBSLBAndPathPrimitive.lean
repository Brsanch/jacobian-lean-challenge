/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.SubsingletonFromBSLBAndPathPrimitive
import JacobianChallenge.Topology.Item14ForwardFromFiniteDim
import JacobianChallenge.Manifold.DiskChartCoverFiniteDim

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 closure from `hSP` + BSLB + path-primitive analytic data

A clean **three-named-hypothesis** route to item 14
(`genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2)`) that avoids the
topological-sphere uniformization input `h_top` entirely:

* **Forward leg:** `ExistsSimplePoleGermAtSomePoint X` (RR existence
  content on the germ field — simple-pole germ exists at some point;
  classically true at `genus X = 0`).
* **Reverse leg** (factored through `SimplyConnectedSpace X`):
  * `h_bslb` — `BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀` (every
    smooth based loop has its singleCycle in `stokesBoundaries`).
    Classical content: smooth Hurewicz on a smoothly simply-connected
    manifold.
  * `h_smooth` — `PathPrimitiveSmoothness ... x₀` (path-primitive of
    every 1-form is `ContMDiff ω`). Classical content: parameter-
    dependent integral smoothness.
  * `h_ftc` — `PathPrimitiveFTC ... x₀` (path-primitive's `mfderiv`
    recovers `om.eval`). Classical content: FTC for line integrals.

Compared to the existing 2-input route `(hSP, h_top)` in
`Item14From2MinimalClassicalInputs.lean`, this route trades the single
topological-sphere uniformization hypothesis for three more elementary
named classical hypotheses — none of which require uniformization itself.

The `[FiniteDimensional ℂ (HolomorphicOneForm X)]` instance needed by
the forward leg is supplied internally from the unconditional
`DiskChartCover.holomorphicOneFormFiniteDim_holds`, so it is **not** a
separate input.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 from a simple-pole germ and BSLB + path-primitive
analytic data.**

Three named classical inputs:

* `hSP` — forward leg (RR-class existence).
* `h_bslb` — reverse leg's smooth Hurewicz content
  (conditional on `SimplyConnectedSpace X`).
* `h_smooth`, `h_ftc` — reverse leg's analytic content
  (also conditional on `SimplyConnectedSpace X`).

The `[FiniteDimensional ℂ (HolomorphicOneForm X)]` instance is
discharged internally from `DiskChartCover.holomorphicOneFormFiniteDim_holds`. -/
theorem genus_eq_zero_iff_homeo_from_hSP_BSLB_pathPrimitive
    (x₀ : X)
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth : SimplyConnectedSpace X →
      PathPrimitiveSmoothness
        (smoothPathConnected_of_preconnected (X := X)) x₀)
    (h_ftc : SimplyConnectedSpace X →
      PathPrimitiveFTC
        (smoothPathConnected_of_preconnected (X := X)) x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  haveI : FiniteDimensional ℂ (HolomorphicOneForm X) :=
    DiskChartCover.holomorphicOneFormFiniteDim_holds (X := X)
  exact genus_eq_zero_iff_homeo_from_existsSimplePoleGerm_and_finiteDim X
    hSP
    (s2ImpliesGenus0_of_BSLB_and_pathPrimitive x₀ h_bslb h_smooth h_ftc)

/-! ## Specialisation: under `Subsingleton (HolomorphicOneForm X)`

When `HolomorphicOneForm X` is already a subsingleton (i.e. `genus X = 0`
is already known via finrank), the analytic per-1-form inputs become
vacuous (the basis is empty). We still need `hSP` for the forward leg
and `h_bslb` for the reverse leg's homeomorphism. -/

/-- **Item 14 under `Subsingleton (HolomorphicOneForm X)` from
`hSP + h_bslb` (path-primitive inputs vacuous).** -/
theorem genus_eq_zero_iff_homeo_from_hSP_BSLB_under_subsingleton
    (x₀ : X) [Subsingleton (HolomorphicOneForm X)]
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) := by
  -- Under Subsingleton, every PathPrimitiveSmoothness / PathPrimitiveFTC
  -- statement is vacuous: ∀ om : HolomorphicOneForm X, ... unfolds to a
  -- proof for the unique element, but Subsingleton means all elements
  -- coincide so we just need it for any single om.
  -- Concretely: every om equals the canonical 0 element, so the
  -- per-om statements collapse to statements about pathPrimitive 0,
  -- which IS smooth (constant 0) and has FTC trivially.
  -- Under Subsingleton, every om = 0, so pathPrimitive om = constant 0.
  have h_path_zero :
      pathPrimitive (smoothPathConnected_of_preconnected (X := X)) x₀
          (0 : HolomorphicOneForm X) = fun _ => (0 : ℂ) := by
    funext x
    exact complexChainPeriod_zero_right _
  refine genus_eq_zero_iff_homeo_from_hSP_BSLB_pathPrimitive x₀ hSP h_bslb
    (fun _ om => ?_) (fun _ om x => ?_)
  · -- PathPrimitiveSmoothness: under Subsingleton, om = 0.
    have h0 : om = 0 := Subsingleton.elim om 0
    subst h0
    rw [h_path_zero]
    exact contMDiff_const
  · -- PathPrimitiveFTC: under Subsingleton, om = 0; both sides are 0.
    have h0 : om = 0 := Subsingleton.elim om 0
    subst h0
    rw [HolomorphicOneForm.eval_zero, h_path_zero, mfderiv_const]
    rfl

end JacobianChallenge

end
