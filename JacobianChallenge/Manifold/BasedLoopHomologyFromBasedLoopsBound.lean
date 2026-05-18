/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Manifold.GenericGenusH1SpansTopFromLoopHomology
import JacobianChallenge.Manifold.StokesBoundariesTopRiemannSphere

set_option linter.unusedSectionVars false

/-! # Per-based-loop homology hypothesis from `BasedSmoothLoopsBoundHypothesis`

The `BasedLoopHomologyDecompositionHypothesis cycleGens p₀` of
`GenericGenusH1SpansTopFromLoopHomology.lean` is a genuine generalization
of `BasedSmoothLoopsBoundHypothesis I X p₀`: at the genus-0 corner
(where `cycleGens` is the empty tuple `Fin.elim0`), it reduces to "every
based loop's `single` lies in `stokesBoundaries`" — i.e. exactly the
genus-0 hypothesis. More generally, whenever a based loop is *itself*
in `stokesBoundaries` (the genus-0 hypothesis applied to a manifold
which happens to have torsion-free π₁), the trivial decomposition
(all coefficients 0) discharges the genus-≥1 hypothesis for **any**
choice of `cycleGens`.

This file ships the trivial subsumption + a `RiemannSphere`-specialized
corollary giving an alternative route to `H1_spans_top_canonical` on
RS via the new genus-≥1 reduction.

## What this file ships

* `BasedLoopHomologyDecompositionHypothesis_of_basedLoopsBound` — the
  trivial subsumption: `BasedSmoothLoopsBoundHypothesis` implies the
  per-loop homology hypothesis for any `cycleGens`.
* `BasedLoopHomologyDecompositionHypothesis_RS` — `RiemannSphere`
  corollary, unconditional via `basedSmoothLoopsBoundHypothesis_RS_holds`.

No `sorry`, no `axiom`. -/

open scoped Manifold Topology Bundle ContDiff

noncomputable section

namespace JacobianChallenge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]

/-- **`BasedLoopHomologyDecompositionHypothesis` from
`BasedSmoothLoopsBoundHypothesis`.**

The genus-0 bound says every based loop's `single` already lies in
`stokesBoundaries`. Then for any choice of `cycleGens`, the trivial
decomposition `n := fun _ => 0` produces
`single γ - ∑ 0 • cycleGens i = single γ ∈ stokesBoundaries`. -/
theorem BasedLoopHomologyDecompositionHypothesis_of_basedLoopsBound
    {g : ℕ} (cycleGens : Fin (2 * g) → SmoothCycle 𝓘(ℝ, ℂ) X)
    (p₀ : X)
    (h_bound : BasedSmoothLoopsBoundHypothesis 𝓘(ℝ, ℂ) X p₀) :
    BasedLoopHomologyDecompositionHypothesis cycleGens p₀ := by
  intro γ h_src h_tgt
  refine ⟨fun _ => 0, ?_⟩
  -- ∑ 0 • cycleGens i = 0, so single γ - 0 = single γ ∈ stokesBoundaries.
  have h_sum_zero :
      (∑ i, (0 : ℤ) • cycleGens i)
        = (0 : SmoothCycle 𝓘(ℝ, ℂ) X) := by
    simp
  rw [h_sum_zero, sub_zero]
  exact h_bound γ h_src h_tgt

/-! ## RiemannSphere specialization (unconditional) -/

namespace RiemannSphere

/-- **`BasedLoopHomologyDecompositionHypothesis` on `RiemannSphere`,
unconditional.**

For any basepoint `p₀ : RiemannSphere`, any genus `g`, and any choice of
`cycleGens : Fin (2*g) → SmoothCycle 𝓘(ℝ, ℂ) RiemannSphere`, the
per-loop homology hypothesis holds via the unconditional genus-0
`basedSmoothLoopsBoundHypothesis_RS_holds`. -/
theorem basedLoopHomologyDecompositionHypothesis_RS_holds
    {g : ℕ}
    (cycleGens : Fin (2 * g) → SmoothCycle 𝓘(ℝ, ℂ) RiemannSphere)
    (p₀ : RiemannSphere) :
    BasedLoopHomologyDecompositionHypothesis cycleGens p₀ :=
  BasedLoopHomologyDecompositionHypothesis_of_basedLoopsBound
    cycleGens p₀ (basedSmoothLoopsBoundHypothesis_RS_holds p₀)

end RiemannSphere

end JacobianChallenge

end
