/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Divisor.PrincipalDivisor
import JacobianChallenge.Manifold.MeromorphicAt

set_option diagnostics.threshold 100

/-! # Convenience builder for `MeromorphicNonzero X` from continuity

If `g : X → ℂ` is meromorphic on all of `X`, continuous everywhere
(stronger than `regular_continuousAt`), and has no identically-zero
germ at any point, then it directly assembles to a
`MeromorphicNonzero X`.

This is the "trivial" case of the lifting: when `g` already satisfies
the strongest form of continuity, no canonicalisation is needed and
the structure builds directly. The substantive `LiftToMeromorphicNonzero`
discharge for arbitrary L(δp) members reduces — under
`GermCoherentLift_Discharge` — to this builder applied to
`germLimitLift g`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Builder.** From `g : X → ℂ` globally meromorphic, continuous,
and nonvanishing-germ at every point, build a `MeromorphicNonzero X`
with `toFun = g`. -/
def MeromorphicNonzero.ofContinuousMeromorphic
    (g : X → ℂ)
    (h_mero : MMeromorphicOn (𝓘(ℂ, ℂ)) g Set.univ)
    (h_nonvanish : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x ≠ ⊤)
    (h_cts : Continuous g) :
    MeromorphicNonzero X where
  toFun := g
  meromorphic := h_mero
  nonvanishing_germ := h_nonvanish
  regular_continuousAt := fun _x _ => h_cts.continuousAt

@[simp] lemma MeromorphicNonzero.ofContinuousMeromorphic_toFun
    (g : X → ℂ)
    (h_mero : MMeromorphicOn (𝓘(ℂ, ℂ)) g Set.univ)
    (h_nonvanish : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) g x ≠ ⊤)
    (h_cts : Continuous g) :
    (MeromorphicNonzero.ofContinuousMeromorphic g h_mero h_nonvanish h_cts).toFun = g := rfl

end JacobianChallenge

end
