/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.Item14ForwardFromCompactConnected
import JacobianChallenge.Topology.S2ImpliesGenus0FromBSLBAndAdmissibility

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! # Item 14 biconditional from `hSP` + `h_bslb` + per-basis admissibility

Composes:

* `genus_eq_zero_iff_homeo_from_existsSimplePoleGerm` (forward leg from
  `hSP`, reverse leg from `S2ImpliesGenus0`); and
* `s2ImpliesGenus0_of_bslb_and_admissibleChartCover` (reverse leg from
  `h_bslb` + per-basis chart-cover admissibility).

The result is a **3-named-input** capstone of item 14:

* `hSP : ExistsSimplePoleGermAtSomePoint X` (forward leg, RR-class).
* `h_bslb : SimplyConnectedSpace X → BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀`
  (reverse leg, period-lattice content).
* `h_admit : SimplyConnectedSpace X → ∀ i, PathPrimitiveAdmissibleChartCover (b i)`
  (reverse leg, chart-cover analytic content: chartLocalPrimitive
  smoothness + FTC over a chart cover).

This is a clean separation of the three substantive components of
item 14: (i) classical RR-existence (forward), (ii) smooth-Hurewicz at
genus 0 (period-lattice on the reverse), and (iii) the analytic
primitive-existence content (chart-local FTC on the reverse).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff
open Module

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X]
  [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Item 14 biconditional from `hSP` + `h_bslb` + per-basis
`PathPrimitiveAdmissibleChartCover`.**

Equivalent to `genus_eq_zero_iff_homeo_from_4_minimal_inputs`
(`Topology/Item14From4MinimalInputs.lean`) but with the
`h_smooth_b` + `h_ftc_b` per-basis analytic hypotheses replaced by the
bundled `PathPrimitiveAdmissibleChartCover (b i)` admissibility
predicate per basis element.

* `hSP` — forward leg (RR-class existence of a simple-pole germ).
* `h_bslb` — reverse leg, period-lattice content (smooth-Hurewicz at
  genus 0).
* `h_admit` — reverse leg, analytic content (chartLocalPrimitive
  smoothness + FTC over a chart cover, applied per basis element). -/
theorem genus_eq_zero_iff_homeo_from_hSP_bslb_and_admissibility
    (x₀ : X) {ι : Type*}
    (b : Basis ι ℂ (HolomorphicOneForm X))
    (hSP : MeromorphicFunctionField.ExistsSimplePoleGermAtSomePoint X)
    (h_bslb : SimplyConnectedSpace X →
      BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X x₀)
    (h_admit : SimplyConnectedSpace X →
      ∀ (i : ι), PathPrimitiveAdmissibleChartCover (b i)) :
    JacobianChallenge.genus X = 0 ↔ Nonempty (X ≃ₜ StandardS2) :=
  genus_eq_zero_iff_homeo_from_existsSimplePoleGerm X hSP
    (s2ImpliesGenus0_of_bslb_and_admissibleChartCover x₀ b h_bslb h_admit)

end JacobianChallenge

end
