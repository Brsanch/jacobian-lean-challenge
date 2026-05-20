/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.S2ImpliesGenus0FromBasedSmoothLoopsBound
import JacobianChallenge.Topology.Item14ForwardFromCompactConnected

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional from the two minimal named hypotheses

Composes `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm` (forward
leg, item 14 forward via `ExistsSimplePoleGermAtSomePoint`) with
`s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis` (reverse leg,
item 14 reverse via the weakest in-tree `BasedSmoothLoopsBoundHypothesis`
input + per-basis smoothness + per-basis FTC + chip D's
`HolomorphicStokesHypothesis_holds_unconditional`).

The resulting reduction needs at each X the following named
classical hypotheses:

* **Forward:** `ExistsSimplePoleGermAtSomePoint X` (RR-class
  existence).
* **Reverse (4 inputs):**
  - `h_conn_from_sc` — `SimplyConnectedSpace X → SmoothPathConnected`.
  - `h_bslb` — `SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis`.
  - `h_smooth_b` — per-basis `ContMDiff ω (pathPrimitive ...)`.
  - `h_ftc_b` — per-basis FTC at `eval`.

On `RiemannSphere`, `basedSmoothLoopsBoundHypothesis_RS_holds` is in
tree. On `ℂ`, `basedSmoothLoopsBoundHypothesis_C_holds` is in tree.

No `sorry`, no `axiom`. -/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from the minimal in-tree-named hypotheses.**

Composition:
* Forward (`genus = 0 → S²`) via
  `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm` (item 14
  forward from `ExistsSimplePoleGermAtSomePoint`).
* Reverse (`S² → genus = 0`) via
  `s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis` (item 14
  reverse from `BasedSmoothLoopsBoundHypothesis` + per-basis
  smoothness + FTC, with chip D supplying the Stokes step).

The five named inputs are the **minimal** classical hypotheses
remaining at this composition level. -/
theorem genus_eq_zero_iff_homeo_from_minimal_inputs
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_conn_from_sc : SimplyConnectedSpace X → SmoothPathConnected 𝓘(ℝ, ℂ) X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_smooth_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι),
      ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ)) ω
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)))
    (h_ftc_b : ∀ (hsc : SimplyConnectedSpace X) (i : ι) (x : X),
      (b i).eval x = mfderiv (𝓘(ℂ, ℂ)) (𝓘(ℂ, ℂ))
        (pathPrimitive (h_conn_from_sc hsc) x₀ (b i)) x) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_existsSimplePoleGerm X hSP
    (s2ImpliesGenus0_of_basedSmoothLoopsBoundHypothesis (X := X) x₀ b
      h_conn_from_sc h_bslb h_smooth_b h_ftc_b)

end JacobianChallenge

end
