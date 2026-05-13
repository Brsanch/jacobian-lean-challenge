/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LimitAtNonPole
import JacobianChallenge.Topology.GermLimitLiftSetup

set_option diagnostics.threshold 100

/-! # `germ_coherent_off`: predicate for clean lifting

The `germLimitLift` operation canonicalises a function at every point
to its punctured-nhd limit. For a `g : X → ℂ` that is already
"germ-coherent" — meaning it already agrees with its own
`germLimitLift` in a punctured nhd of every point — the lift
operation is the identity, and standard ContinuousAt-style
properties propagate.

This file ships the predicate and basic API: a tier-2 reduction
naming the property that, when discharged on `g ∈ L(δp)`, would
close the `LiftToMeromorphicNonzero` discharge (zz362).

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **`g : X → ℂ` is germ-coherent off `p`** iff on every punctured
neighbourhood of every `x ≠ p`, `g` agrees with its germLimit-based
canonicalisation. -/
def GermCoherentOff (p : X) (g : X → ℂ) : Prop :=
  ∀ x, x ≠ p → germLimitLift g =ᶠ[𝓝[≠] x] g

/-- **The germLimitLift of `g` is automatically germ-coherent off any
point.** Tautological: at every `x`, the germ of `germLimitLift g`
in a punctured nhd of `x` equals the germ of `g` (because the
punctured-nhd limit is captured by `germLimit`, which we then re-
apply pointwise — but the second application doesn't change the
pointwise values away from `x`). Pending a non-trivial proof in a
downstream chip; named here as the cleanest single classical step. -/
def GermCoherentLift_Discharge (p : X) : Prop :=
  ∀ (g : X → ℂ), IsBoundedByDeltaP p g →
    GermCoherentOff p (germLimitLift g)

/-- **Punctured-nhd Tendsto of `germLimitLift g`** at non-pole
points, from germ-coherence and L(δp). For `g ∈ L(δp)` and germ-
coherent off `p`, at any non-pole `x`, the germLimitLift converges
to the same limit `c` as `g` does (via zz365's Tendsto). -/
theorem germLimitLift_tendsto_punctured_of_germCoherent
    {p : X} {g : X → ℂ}
    (hg : IsBoundedByDeltaP p g) (h_coh : GermCoherentOff p g)
    {x : X} (hx : x ≠ p) :
    ∃ c : ℂ, Filter.Tendsto (germLimitLift g) (𝓝[≠] x) (𝓝 c) := by
  obtain ⟨c, h_tend⟩ :=
    exists_tendsto_punctured_of_isBoundedByDeltaP_off_p hg hx
  -- germLimitLift g =ᶠ[𝓝[≠] x] g by h_coh.
  refine ⟨c, ?_⟩
  exact h_tend.congr' (h_coh x hx).symm

end JacobianChallenge

end
