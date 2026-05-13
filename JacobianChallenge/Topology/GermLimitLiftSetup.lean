/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import JacobianChallenge.Topology.LinearSystemAPI
import JacobianChallenge.Divisor.PrincipalDivisor

set_option diagnostics.threshold 100

/-! # First setup steps for `LiftToMeromorphicNonzero` via `germLimit`

zz362 named `LiftToMeromorphicNonzero X` as the technical hypothesis
bridging `g : X → ℂ` in `L(δp) \ constants` to a `MeromorphicNonzero
X` carrier. The classical construction is via the `germLimit`
canonical-value function (already in
`Divisor/PrincipalDivisor.lean`).

This chip provides the *foundational setup* for the discharge:

* `germLimitLift` — the canonicalised lift `g'(x) := MeromorphicNonzero.germLimit g x`
  for `x` non-pole (and `g x` at poles); equivalently
  `MeromorphicNonzero.germLimit g x` everywhere when `g` is `IsBoundedByDeltaP p`-
  bounded.

The full discharge of `LiftToMeromorphicNonzero` requires:
* Identity theorem propagation (nonvanishing-germ globalisation).
* Order-preservation under germLimit.
* Continuity at non-pole points.
* Non-constancy preservation.

Each is a separate substantive step. This chip just sets up the
definitional carrier; the existence proof of the *full* lift is the
next-chip target.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

namespace JacobianChallenge

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **The germLimit-based lift candidate** for `g : X → ℂ`. At every
point `x`, return `MeromorphicNonzero.germLimit g x` — which equals the analytic
continuation limit when `g` has a finite limit at `x` (the standard
case for `g ∈ L(δp)` at non-pole points) and falls back to `g x`
otherwise. -/
noncomputable def germLimitLift (g : X → ℂ) : X → ℂ :=
  fun x => MeromorphicNonzero.germLimit g x

/-- **Pointwise definition unfold.** -/
@[simp] lemma germLimitLift_apply (g : X → ℂ) (x : X) :
    germLimitLift g x = MeromorphicNonzero.germLimit g x := rfl

/-- **The lift agrees with `g` where `g` is already continuous and
has a punctured-nhd limit equal to `g x`.** This is a tautology at
the level of `germLimit`, but it pins down the construction. -/
lemma germLimitLift_eq_self_of_continuousAt
    {g : X → ℂ} {x : X} (h_cts : ContinuousAt g x) :
    germLimitLift g x = g x := by
  -- ContinuousAt g x ⇒ Tendsto g (𝓝 x) (𝓝 (g x)) ⇒ Tendsto g (𝓝[≠] x) (𝓝 (g x)).
  have h_tendsto : Filter.Tendsto g (𝓝[≠] x) (𝓝 (g x)) :=
    h_cts.tendsto.mono_left nhdsWithin_le_nhds
  simp [germLimitLift, MeromorphicNonzero.germLimit_eq_of_tendsto h_tendsto]

/-- **The lift of the zero function is the zero function.** -/
@[simp] lemma germLimitLift_zero :
    germLimitLift (0 : X → ℂ) = (0 : X → ℂ) := by
  ext x
  -- The constant zero function is continuous everywhere; germLimitLift = self.
  exact germLimitLift_eq_self_of_continuousAt continuousAt_const

/-- **The lift of the constant function `c` is the constant function
`c`.** -/
@[simp] lemma germLimitLift_const (c : ℂ) :
    germLimitLift (fun _ : X => c) = (fun _ : X => c) := by
  ext x
  exact germLimitLift_eq_self_of_continuousAt continuousAt_const

/-- **A globally continuous function is its own lift.** If `g` is
continuous at every point, then `germLimitLift g = g`. -/
lemma germLimitLift_eq_self_of_continuous {g : X → ℂ}
    (h_cts : Continuous g) :
    germLimitLift g = g := by
  ext x
  exact germLimitLift_eq_self_of_continuousAt h_cts.continuousAt

/-- **`germLimitLift` is invariant under punctured-nhd EventuallyEq
when at least one of the functions has a limit.** -/
lemma germLimitLift_eq_of_eventuallyEq_nhdsNE_of_tendsto {f g : X → ℂ}
    {x : X} (h : f =ᶠ[𝓝[≠] x] g) {c : ℂ}
    (hc : Filter.Tendsto g (𝓝[≠] x) (𝓝 c)) :
    germLimitLift f x = germLimitLift g x := by
  show MeromorphicNonzero.germLimit f x = MeromorphicNonzero.germLimit g x
  -- Both have limit c (via EventuallyEq).
  have hc_f : Filter.Tendsto f (𝓝[≠] x) (𝓝 c) := hc.congr' h.symm
  rw [MeromorphicNonzero.germLimit_eq_of_tendsto hc_f,
      MeromorphicNonzero.germLimit_eq_of_tendsto hc]

end JacobianChallenge

end
