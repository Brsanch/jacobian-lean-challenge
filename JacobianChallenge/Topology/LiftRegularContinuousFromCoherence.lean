/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LiftDecomposition
import JacobianChallenge.Topology.GermCoherent
import JacobianChallenge.Topology.LimitAtNonPole

set_option diagnostics.threshold 100

/-! # Substantive reduction: regular-continuity at non-pole points from
universal germ-coherence

This file ships a substantive **architectural reduction**: at every
non-pole point `x ≠ p`, `ContinuousAt (germLimitLift g) x` is
derivable from a single named "universal germ-coherence" hypothesis
on `L(δp)` members. The discharge avoids the technical
`LiftOrderPreserved`/`GermCoherentLift_Discharge` interplay by going
directly from coherence-of-`g` to continuity-of-`germLimitLift g`.

## Hypothesis named here

  `UniversalGermCoherent X p` :=
    ∀ g : X → ℂ, IsBoundedByDeltaP p g → GermCoherentOff p g

i.e. every L(δp) element is germ-coherent off `p`. This is precisely
the "identity-theorem + analytic continuation" content: the literal
function values of any meromorphic-bounded-by-δp function agree with
their punctured-nhd germ limits away from `p`.

## What this chip proves

Under `UniversalGermCoherent X p`, `ContinuousAt (germLimitLift g) x`
follows directly for every `g ∈ L(δp)` and every `x ≠ p`. The proof
is the mathlib-clean composition of:

* zz365's `exists_tendsto_punctured_of_isBoundedByDeltaP_off_p` —
  ∃ c, `Tendsto g (𝓝[≠] x) (𝓝 c)`.
* zz365's value identification — `germLimitLift g x = c`.
* `UniversalGermCoherent`'s `GermCoherentOff p g` —
  `germLimitLift g =ᶠ[𝓝[≠] x] g`, transferring the Tendsto from g
  to `germLimitLift g`.
* mathlib's `continuousAt_iff_punctured_nhds`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Named hypothesis: every L(δp) member is germ-coherent off `p`.**
This is the identity-theorem / analytic-continuation content: pointwise
values of any meromorphic-bounded-by-δp function agree with their
punctured-nhd germ limits at every non-pole point. -/
def UniversalGermCoherent (p : X) : Prop :=
  ∀ g : X → ℂ, IsBoundedByDeltaP p g → GermCoherentOff p g

/-- **Substantive discharge:** at every non-pole point, the
canonicalised lift is `ContinuousAt`. -/
theorem continuousAt_germLimitLift_off_p_of_universalGermCoherent
    {p : X} (h_univ_coh : UniversalGermCoherent X p)
    {g : X → ℂ} (hg_in : IsBoundedByDeltaP p g)
    {x : X} (hxp : x ≠ p) :
    ContinuousAt (germLimitLift g) x := by
  -- 1. germ-coherence of g at x (from the universal hypothesis).
  have h_coh : germLimitLift g =ᶠ[𝓝[≠] x] g :=
    h_univ_coh g hg_in x hxp
  -- 2. From zz365: ∃ c, Tendsto g (𝓝[≠] x) (𝓝 c) and germLimitLift g x = c.
  obtain ⟨c, h_tend, h_val⟩ :=
    germLimitLift_eq_punctured_limit_of_isBoundedByDeltaP_off_p hg_in hxp
  -- 3. Transfer Tendsto from g to germLimitLift g via the EventuallyEq.
  have h_tend_lift : Tendsto (germLimitLift g) (𝓝[≠] x) (𝓝 c) :=
    h_tend.congr' h_coh.symm
  -- 4. Apply continuousAt_iff_punctured_nhds.
  rw [continuousAt_iff_punctured_nhds, h_val]
  exact h_tend_lift

end JacobianChallenge

end
